open Tree

type t

val create :
  ?is_specification:bool -> ?entry_locals:Core.local list -> ?takes_free_locals:bool -> unit -> t

val for_lambda : t -> t
val is_specification : t -> bool
val entry_locals : t -> Core.local list
val new_local : t -> local_kind -> Types.ty -> Core.origin -> local
val local_info : t -> local -> local_info
val temporary : t -> Types.ty -> Core.origin -> local
val add_temporary : t -> local -> unit
val at : local -> place
val source : t -> Core.local -> local option
val add_source : t -> Core.local -> local -> unit
val free_source : t -> Core.local -> type_:Types.ty -> origin:Core.origin -> local

val bind_source :
  ?name:string -> ?is_var:bool -> t -> Core.local -> Types.mode -> Types.ty -> Core.origin -> local

val register_binding : t -> local -> unit
val note_bound_to_place : t -> local -> unit
val place_temporary : t -> node:Core.id -> Types.ty -> Core.origin -> local
val free_locals : t -> local list
val emit : t -> in_tree statement_kind -> Core.origin -> unit
val assign : ?node:Core.id -> t -> place -> rvalue -> Core.origin -> unit
val hold : ?node:Core.id -> t -> Types.ty -> Core.origin -> rvalue -> operand option
val held : t -> operand -> Types.ty -> Core.origin -> operand
val borrowed_place : t -> place -> place
val jump : t -> jump -> Core.origin -> unit
val reaches : t -> bool
val mark_unreachable : t -> unit
val block_of : t -> (unit -> operand option) -> block

type suspended

val suspend_block : t -> suspended
val resume_block : t -> suspended -> statement list
val emitted : t -> statement list
val start_loan : t -> operand -> Types.mode -> loan_duration -> Core.origin -> int
val end_loans : t -> int list -> Core.origin -> unit

type scope
type held

val in_scope : ?provides:bool -> ?held:held -> t -> Core.origin -> (unit -> 'a) -> 'a
val in_statement : t -> Core.origin -> (unit -> 'a) -> 'a

val in_value_scope :
  ?provides:bool -> t -> Core.origin -> (unit -> operand option) -> operand option

val in_arm_scope : t -> (scope -> 'a) -> 'a
val end_scope : t -> scope -> Core.origin -> unit
val dead_in : scope -> Core.origin -> statement list

type condition_lends = For_statement | For_block | For_condition

val in_condition_scope :
  lends:condition_lends -> t -> (unit -> 'value) -> 'value * scope * scope * held

val in_old : t -> (unit -> 'a) -> 'a
val reads_entry : t -> Core.local -> bool
val binding_to_statement : t -> (unit -> 'a) -> 'a
val extending : t -> Core.id list -> (unit -> 'a) -> 'a
val deferring : t -> (unit -> 'a) -> 'a * local list
val with_compound_target : t -> place -> (unit -> 'a) -> 'a
val compound_target : t -> place option
val looping : t -> (unit -> unit) -> unit
val in_task : t -> task -> (unit -> 'a) -> 'a
val start_group : t -> Core.origin -> Core.origin -> unit
val resume_group : t -> Core.origin -> Core.origin -> unit
val return_ : t -> operand option -> Core.origin -> unit
val break_ : t -> Core.origin -> unit
val continue_ : t -> Core.origin -> unit
val add_lambda : t -> body -> int
val lambdas : t -> body array

val finish :
  ?captures:local list ->
  ?is_functional:bool ->
  ?value_type:Types.ty ->
  t ->
  parameters:local list ->
  body

val formula :
  t -> origin:Core.origin -> type_:Types.ty -> (unit -> local list * operand option) -> formula

val unit_value : operand
