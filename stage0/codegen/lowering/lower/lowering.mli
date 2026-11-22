type cleanup =
  | Drop_value of Lowered.place
  | Drop_flagged of { place : Lowered.place; flag : Lowered.place }
  | Free_pointed of Lowered.place
  | Join_group of Lowered.statement

type scope_kind = Bindings | Statement
type scope = { kind : scope_kind; mutable owned : cleanup list }

type loop = {
  continue_ : Lowered.block;
  continue_depth : int;
  break_ : Lowered.block;
  break_depth : int;
}

type lending = {
  slot : Lowered.place option;
  part : Ground.ty;
  record : Lowered.operand;
  arena : Lowered.operand;
  site : Lowered.operand;
}

type frame = {
  code : Definitions.code;
  mutable self_place : Lowered.place option;
  exit : (Lowered.block * int) option;
  mir : mir_frame option;
}

and mir_frame = {
  body : Mir.Graph.body;
  lambdas : Mir.Graph.body array;
  places : (Mir.local, Lowered.place) Hashtbl.t;
  owner : scope option;
  returns_into : Lowered.place option;
  mutable provides : (Path.t * Lowered.operand) list list;
  returned : Mir.local list;
  mutable taken : Mir.place list;
  moves : Moves.t;
  flags : (Moves.path * Lowered.place) list;
  mutable move_state : Moves.state;
  lending : lending option;
  called_parts : Mir.local list;
  lend_records : (Mir.local, Lowered.place) Hashtbl.t;
  placed_parts : (Mir.local, unit) Hashtbl.t;
  mutable forwarded_locals : int;
  ended_after_lend : Mir.local list;
  after_lend : bool array;
  mutable block : Mir.Graph.block;
}

type task = { id : Mir.task; group : Lowered.place; end_block : Lowered.block; scope_depth : int }

type spawn_loop = {
  task : Mir.task;
  group : Lowered.place;
  item : Lowered.local;
  element : Ground.ty;
}

type schedule = Sequential | Chunked | Spawned of spawn_loop
type result_slot = Through of Lowered.local | Returned_in of Lowered.local | No_result

type state = {
  context : Definitions.context;
  mutable frame : frame;
  builder : Emit_c.Ir_builder.t;
  mutable scopes : scope list;
  mutable loops : loop list;
  mutable result : result_slot;
  nested : int ref;
  mutable evidence : (Path.t * Lowered.operand) list;
  mutable tasks : task list;
  mutable moved : Lowered.place list;
  mutable lend_arena : Lowered.operand option;
}

val make_frame : Definitions.code -> frame
val enter : Definitions.context -> ?nested:int ref -> builder:Emit_c.Ir_builder.t -> frame -> state
val enter_item : Definitions.context -> item:Lowered.Item.t -> Definitions.code -> state
val may_fork : state -> bool
val allocate_local : state -> ?name:string -> Lowered.ty -> Lowered.place
val outline : state -> parts:Lowered.local list -> (unit -> unit) -> int * Lowered.operand
val ground : state -> Types.ty -> Ground.ty
val is_trivial : state -> Ground.ty -> bool
val is_zero_size : state -> Ground.ty -> bool
val make_site : state -> Source.Definition_span.t -> Lowered.site

type unsupported = { construct : string; at : Lowered.site option }

exception Unsupported of unsupported

val raise_unsupported : ?at:Lowered.site -> ('a, unit, string, 'b) format4 -> 'a
val require_written : state -> Definitions.written
val quote_span : state -> Source.Definition_span.t -> string
val lookup_innermost_scope : state -> scope
val allocate_temporary : state -> Ground.ty -> Lowered.place
val allocate_binding : state -> Ground.ty -> Lowered.place
val allocate_flagged_binding : state -> Ground.ty -> flag:Lowered.place -> Lowered.place

val allocate_parameter :
  state ->
  ?in_scope:bool ->
  ?name:string ->
  owned:bool ->
  Language.Mode.t ->
  Ground.ty ->
  Lowered.local option * Lowered.place

val list_evidence_parameters : state -> Path.t list -> Lowered.local list
val look_up_capabilities : state -> table:Lowered.operand -> Path.t list -> unit
val find_panic_trace : state -> Lowered.operand option
val set_result_slot : state -> Convention.result -> unit
val find_result_place : state -> Lowered.place option
val return_result : state -> Lowered.terminator
val leave_to : state -> int -> unit
val open_scope : state -> scope_kind -> scope
val close_scope : state -> scope -> unit
val run_in_scope : state -> (unit -> 'a) -> 'a
val run_in_statement : state -> (unit -> 'a) -> 'a

val finish_function :
  state ->
  ?returns:bool ->
  first:Lowered.local list ->
  rest:Lowered.local list ->
  unit ->
  Emit_c.Ir_builder.prototype

val finish_item : state -> ?returns:bool -> rest:Lowered.local list -> unit -> Emit_c.fragment
val emit_unreachable_block : state -> unit
val move_place : state -> Lowered.place -> Lowered.operand
val make_owned_operand : state -> Lowered.place -> Ground.ty -> Lowered.operand
val take : state -> Lowered.place -> Ground.ty -> destination:Lowered.place -> unit
val snapshot : state -> Lowered.place -> Lowered.place

val run_in_loop :
  state -> continue_:Lowered.block -> break_:Lowered.block -> depth:int -> (unit -> unit) -> unit

val find_place_type : state -> Lowered.place -> Lowered.ty option
val is_reached_through_pointer : state -> Lowered.place -> bool
val make_int_constant : Memory_layout.integer -> Z.t -> Lowered.operand
val classify_scalar : state -> Ground.ty -> Memory_layout.scalar
