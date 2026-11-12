type cleanup =
  | Drop_value of Lir.place
  | Free_pointed of Lir.place
  | Give_back of { lent : Lir.place; source : Lir.place; ty : Ground.ty }
  | Finish_lend of lend
  | Join_group of Lir.statement

and lend = {
  resume : Lir.block;
  finished : Lir.block;
  selector : Lir.local;
  mutable ways : Lir.block list;
  owned : Lir.place list;
}

type scope_kind = Bindings | Statement
type scope = { kind : scope_kind; mutable owned : cleanup list }
type loop = { continue_ : Lir.block; continue_depth : int; break_ : Lir.block; break_depth : int }

type frame = {
  code : Definitions.code;
  bindings : (Definitions.S.id, Lir.place) Hashtbl.t;
  synthetic : (int, Lir.place) Hashtbl.t;
  mutable self_place : Lir.place option;
  on_yield : (Lir.place -> owned:bool -> resume:Lir.block -> stop:Lir.block -> unit) option;
  yield_into : Lir.place option;
  inlined : Path.t list;
  reported : Lir.site option;
  exit : (Lir.block * int) option;
}

type early_exits = {
  winner : Lir.place;
  mutable return_value : Lir.place option;
  scope : scope;
  mutable exits : (Core.task list * Core.expression) list;
}

type task = {
  id : Core.task;
  group : Lir.place;
  early_exits : early_exits;
  end_block : Lir.block;
  scope_depth : int;
}

type spawn_loop = {
  origin : Core.origin;
  group : Lir.place;
  early_exits : early_exits;
  item : Lir.local;
  element : Ground.ty;
}

type schedule = Sequential | Chunked | Spawned of spawn_loop
type result_slot = Through of Lir.local | Returned_in of Lir.local | No_result

type state = {
  context : Definitions.context;
  mutable frame : frame;
  b : Lir_builder.t;
  mutable scopes : scope list;
  mutable loops : loop list;
  mutable result : result_slot;
  nested : Lir.function_ option list ref;
  mutable evidence : (Path.t * Lir.operand) list;
  mutable compound_target : Lir.place option;
  pulling : bool;
  mutable forks : int;
  mutable tasks : task list;
  mutable next_range : schedule;
}

val frame_of : Definitions.code -> inlined:Path.t list -> frame

val enter :
  Definitions.context -> ?pulling:bool -> ?nested:Lir.function_ option list ref -> frame -> state

val may_fork : state -> bool
val fresh_fork : state -> int
val new_early_exits : state -> early_exits
val ground : state -> Types.ty -> Ground.ty
val trivial : state -> Ground.ty -> bool
val is_zero_size : state -> Ground.ty -> bool
val site : state -> Definitions.S.span -> Lir.site

type unsupported = { what : string; at : Lir.site option }

exception Unsupported of unsupported

val unsupported : ?at:Lir.site -> ('a, unit, string, 'b) format4 -> 'a
val source : state -> Definitions.S.span -> string
val innermost_scope : state -> scope
val own_in_scope : state -> Lir.place -> unit
val free_in_scope : state -> Lir.place -> unit
val owned_local : state -> ?name:string -> scope -> Ground.ty -> Lir.place
val temporary : state -> ?name:string -> Ground.ty -> Lir.place
val binding : state -> ?name:string -> Ground.ty -> Lir.place

val parameter :
  state ->
  ?how:(Ground.mode -> Ground.ty -> Lir.ty option) ->
  owned:bool ->
  Ground.mode ->
  Ground.ty ->
  Lir.local option * Lir.place

val evidence_parameters : state -> Path.t list -> Lir.local list
val result_slot : state -> Convention.result -> unit
val result_place : state -> Lir.place option
val returned_type : state -> Ground.ty option
val clear_result : state -> unit
val return_result : state -> Lir.terminator
val drop_scope : state -> scope -> unit
val leave_to : state -> int -> unit
val open_scope : state -> scope_kind -> scope
val pop_scope : state -> scope -> unit
val close_scope : state -> scope -> unit
val in_scope : state -> (unit -> 'a) -> 'a
val in_statement : state -> (unit -> 'a) -> 'a

val finish_function :
  state -> ?returns:bool -> first:Lir.local list -> rest:Lir.local list -> unit -> Lir.function_

val nested_functions : state -> Lir.function_ array
val unreachable_block : state -> unit
val owned : state -> Lir.place -> Ground.ty -> Lir.operand
val take : state -> Lir.place -> Ground.ty -> destination:Lir.place -> unit
val snapshot : state -> Lir.place -> Lir.place

val looping :
  state -> continue_:Lir.block -> break_:Lir.block -> depth:int -> (unit -> unit) -> unit

val replace : state -> Lir.place -> Ground.ty -> by:Lir.place -> unit
val constant_int : Memory_layout.integer -> Z.t -> Lir.operand
val scalar_of : state -> Ground.ty -> Memory_layout.scalar
