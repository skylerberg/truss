val register_call : ?function_value:Syntax.expression -> State.state -> Syntax.expression -> unit
val register_index : State.state -> Syntax.expression -> unit
val build_numeric_literal : State.state -> Syntax.id -> Core.kind
val read_type : State.state -> Syntax.expression -> Types.ty
val build_function_value : State.state -> Syntax.expression -> Core.kind
val build_variant_value : State.state -> Syntax.expression -> Path.t -> string -> Core.kind
val read_local_type : State.state -> Syntax.id -> Types.ty
val build_local_use : State.state -> origin:Core.origin -> Syntax.id -> Core.kind
val read_self_type : State.state -> State.env -> Types.ty
val build_self_local : State.state -> State.env -> origin:Core.origin -> Core.place
val build_constant_place : State.state -> origin:Core.origin -> Path.t -> Core.place

val build_range_record :
  State.state ->
  Syntax.expression ->
  Syntax.expression option ->
  Syntax.expression option ->
  inclusive:bool ->
  Core.kind

val list_capability_impls : State.state -> Types.ty -> (Core.provided * Types.impl_interface) list
val build_provide : State.state -> Syntax.expression list -> Syntax.block -> Core.kind
val build_untagged_string : State.state -> origin:Core.origin -> Syntax.string_literal -> Core.kind

val build_tagged_string :
  State.state -> Syntax.expression -> Syntax.string_literal -> part:Types.ty -> Core.kind

val build_constant_pattern : State.state -> Syntax.id -> Core.pattern_constant -> Core.pattern_kind
val build_named_constant : State.state -> Syntax.id -> Core.pattern_constant
val build_literal_constant : State.state -> Syntax.id -> Syntax.literal -> Core.pattern_constant
val build_range_bound : State.state -> Syntax.range_end -> Core.range_bound

val build_pattern_fields :
  State.state -> Types.field list -> (string * Syntax.pattern) list -> (string * Core.pattern) list

val convert_to_operation : Syntax.operation -> Intrinsic.scalar

val build_operator :
  State.state -> Syntax.expression -> Intrinsic.scalar -> Syntax.expression list -> Core.kind

val build_built_in_comparison :
  State.state -> Syntax.comparison -> Syntax.expression -> Syntax.expression -> Core.kind

val build_comparison :
  State.state ->
  Syntax.expression ->
  Syntax.comparison ->
  Syntax.expression ->
  Syntax.expression ->
  Core.kind

val is_executable : State.state -> Core.expression -> bool
val binds_lent_part : State.state -> Core.expression -> bool

val build_compound_assign :
  State.state ->
  Syntax.statement ->
  Syntax.expression ->
  Syntax.expression ->
  Syntax.operation ->
  Core.statement_kind

val lend_statements : State.state -> Types.mode -> Core.expression -> Core.statement list
val lend_block : State.state -> Types.mode -> Core.block -> Core.block

val quantify_over_elements :
  State.state ->
  Syntax.expression ->
  count:Tables.call ->
  element:Tables.call ->
  lends:Types.mode ->
  origin:Core.origin ->
  (Core.elements -> Core.kind) ->
  Core.kind

val build_for_loop :
  State.state ->
  Syntax.statement ->
  Syntax.expression ->
  pattern:Core.pattern ->
  clauses:Core.loop_clause list ->
  body:Core.block ->
  mode:Core.loop_mode ->
  Core.statement_kind

val build_cost : State.state -> origin:Core.origin -> Syntax.cost -> Core.cost
val build_loop_clause : State.state -> Syntax.loop_clause -> Core.loop_clause

val build_try :
  State.state -> Syntax.expression -> Syntax.expression -> output:Types.ty -> Core.kind

val build_collection_literal : State.state -> Syntax.expression -> Core.expression list -> Core.kind

val build_converted_literal :
  State.state -> Syntax.expression -> element:Types.ty -> Core.expression list -> Core.kind

val build_converted_map_literal :
  State.state ->
  Syntax.expression ->
  key:Types.ty ->
  value_type:Types.ty ->
  (Core.expression * Core.expression) list ->
  Core.kind

val build_declared_local : State.state -> Syntax.id -> Core.local
