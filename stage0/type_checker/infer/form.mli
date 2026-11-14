module Impls = Interface.Impls
module Properties = Interface.Properties

val operand : Types.mode -> Core.expression -> Core.operand
val evidence : Tables.evidence -> Core.evidence
val register_call : ?function_value:Syntax.expression -> State.state -> Syntax.expression -> unit
val register_index : State.state -> Syntax.expression -> unit
val numeric_literal : State.state -> Syntax.id -> Core.kind
val type_of : State.state -> Syntax.expression -> Types.ty
val function_value : State.state -> Syntax.expression -> Core.kind
val variant_value : State.state -> Syntax.expression -> Path.t -> string -> Core.kind
val local_type : State.state -> Syntax.id -> Types.ty
val local_use : State.state -> origin:Core.origin -> Syntax.id -> Core.kind
val self_type : State.state -> State.env -> Types.ty
val self_local : State.state -> State.env -> origin:Core.origin -> Core.place
val constant_place : State.state -> origin:Core.origin -> Path.t -> Core.place

val range_record :
  State.state ->
  Syntax.expression ->
  Syntax.expression option ->
  Syntax.expression option ->
  inclusive:bool ->
  Core.kind

val capability_impls : State.state -> Types.ty -> (Core.provided * Types.impl_interface) list
val provide : State.state -> Syntax.expression list -> Syntax.block -> Core.kind
val untagged_string : State.state -> origin:Core.origin -> Syntax.string_literal -> Core.kind

val tagged_string :
  State.state -> Syntax.expression -> Syntax.string_literal -> part:Types.ty -> Core.kind

val pattern_type : State.state -> Syntax.id -> Types.ty

val equal_to_pattern :
  State.state -> origin:Core.origin -> Types.ty -> Core.kind -> Core.pattern_kind

val pattern_constant : State.state -> Syntax.id -> Core.kind
val pattern_literal : State.state -> Syntax.id -> Syntax.literal -> Core.kind

val pattern_fields :
  State.state -> Types.field list -> (string * Syntax.pattern) list -> (string * Core.pattern) list

val operation_of : Syntax.binary -> Intrinsic.operation

val operator :
  State.state -> Syntax.expression -> Intrinsic.operation -> Syntax.expression list -> Core.kind

val built_in_comparison :
  State.state -> Syntax.binary -> Syntax.expression -> Syntax.expression -> Core.kind

val comparison :
  State.state ->
  Syntax.expression ->
  Syntax.binary ->
  Syntax.expression ->
  Syntax.expression ->
  Core.kind

val is_executable : State.state -> Core.expression -> bool

val binds_lent_part : State.state -> Core.expression -> bool
(** The [binds_lent_part] of an [if] or a [while] with this condition. *)

val compound_assign :
  State.state ->
  Syntax.statement ->
  Syntax.expression ->
  Syntax.expression ->
  Syntax.binary ->
  Core.statement_kind

val lend_statements : State.state -> Types.mode -> Core.expression -> Core.statement list
(** The statements that lend the value of a tail expression of a lending method. *)

val lend_block : State.state -> Types.mode -> Core.block -> Core.block
(** A block whose value a lending method lends, as a block that lends it and has no value. *)

val over_elements :
  State.state ->
  Syntax.expression ->
  count:Tables.call ->
  element:Tables.call ->
  lends:Types.mode ->
  origin:Core.origin ->
  (Core.elements -> Core.kind) ->
  Core.kind
(** The core form of a quantifier that runs as a loop over the elements of a collection, made from
    how the loop visits them. *)

val for_loop :
  State.state ->
  Syntax.statement ->
  Syntax.expression ->
  pattern:Core.pattern ->
  clauses:Core.loop_clause list ->
  body:Core.block ->
  mode:Core.loop_mode ->
  Core.statement_kind
(** The core form of a [for] loop over an iterable expression. *)

val cost : State.state -> origin:Core.origin -> Syntax.cost -> Core.cost
val loop_clause : State.state -> Syntax.loop_clause -> Core.loop_clause
val try_ : State.state -> Syntax.expression -> Syntax.expression -> output:Types.ty -> Core.kind
val collection_literal : State.state -> Syntax.expression -> Core.expression list -> Core.kind

val map_literal :
  State.state -> Syntax.expression -> (Core.expression * Core.expression) list -> Core.kind
