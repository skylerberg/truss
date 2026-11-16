type t

val create :
  ?is_specification:bool -> entry_locals:Core.local list -> ?takes_free_locals:bool -> unit -> t

val make_lambda_builder : t -> t
val is_specification : t -> bool
val entry_locals : t -> Core.local list
val allocate_local : t -> Tree.local_kind -> Types.ty -> Core.origin -> Tree.local
val lookup_local_info : t -> Tree.local -> Tree.local_info
val allocate_temporary : t -> Types.ty -> Core.origin -> Tree.local
val add_temporary : t -> Tree.local -> unit
val make_local_place : Tree.local -> Tree.place
val find_source : t -> Core.local -> Tree.local option
val add_source : t -> Core.local -> Tree.local -> unit
val obtain_free_source : t -> Core.local -> type_:Types.ty -> origin:Core.origin -> Tree.local

val bind_source :
  ?is_var:bool -> t -> Core.local -> Types.mode -> Types.ty -> Core.origin -> Tree.local

val register_binding : t -> Tree.local -> unit
val note_bound_to_place : t -> Tree.local -> unit
val allocate_place_temporary : t -> node:Core.id -> Types.ty -> Core.origin -> Tree.local
val free_locals : t -> Tree.local list
val emit : t -> Tree.statement_kind -> Core.origin -> unit
val assign : t -> Tree.place -> Tree.rvalue -> Core.origin -> unit
val hold : t -> Types.ty -> Core.origin -> Tree.rvalue -> Tree.operand option
val hold_choice : t -> Types.ty -> Core.origin -> Tree.choice -> Tree.operand option
val hold_operand : t -> Tree.operand -> Types.ty -> Core.origin -> Tree.operand
val borrow_place : t -> Tree.place -> Tree.place
val jump : t -> Tree.jump -> Core.origin -> unit
val reaches : t -> bool
val mark_unreachable : t -> unit
val build_block : t -> (unit -> Tree.operand option) -> Tree.block

type suspended

val suspend_block : t -> suspended
val resume_block : t -> suspended -> Tree.statement list
val emitted : t -> Tree.statement list
val start_loan : t -> Tree.operand -> Types.mode -> Tree.loan_duration -> Core.origin -> int
val end_loans : t -> int list -> Core.origin -> unit

type scope
type held

val run_in_scope : ?provides:bool -> ?held:held -> t -> Core.origin -> (unit -> 'a) -> 'a
val run_in_statement : t -> Core.origin -> (unit -> 'a) -> 'a

val run_in_value_scope :
  ?provides:bool -> t -> Core.origin -> (unit -> Tree.operand option) -> Tree.operand option

val run_in_arm_scope : t -> (scope -> 'a) -> 'a
val end_scope : t -> scope -> Core.origin -> unit
val make_dead_statements : scope -> Core.origin -> Tree.statement list

type condition_lends = For_statement | For_block | For_condition

val run_in_condition_scope :
  lends:condition_lends -> t -> (unit -> 'value) -> 'value * scope * scope * held

val run_in_old : t -> (unit -> 'a) -> 'a
val reads_entry : t -> Core.local -> bool
val run_binding_to_statement : t -> (unit -> 'a) -> 'a
val run_extending : t -> Core.id list -> (unit -> 'a) -> 'a
val run_deferring : t -> (unit -> 'a) -> 'a * Tree.local list
val with_compound_target : t -> Tree.place -> (unit -> 'a) -> 'a
val compound_target : t -> Tree.place option
val run_in_loop : t -> (unit -> unit) -> unit
val run_in_task : t -> Tree.task -> (unit -> 'a) -> 'a
val start_group : t -> Core.origin -> Core.origin -> unit
val resume_group : t -> Core.origin -> Core.origin -> unit
val return_ : t -> Tree.operand option -> Core.origin -> unit
val break_ : t -> Core.origin -> unit
val continue_ : t -> Core.origin -> unit
val add_lambda : t -> Tree.body -> int
val lambdas : t -> Tree.body array

val finish :
  ?captures:Tree.local list ->
  ?is_functional:bool ->
  ?value_type:Types.ty ->
  t ->
  parameters:Tree.local list ->
  Tree.body

val build_formula :
  t ->
  origin:Core.origin ->
  type_:Types.ty ->
  (unit -> Tree.local list * Tree.operand option) ->
  Tree.formula

val unit_value : Tree.operand
