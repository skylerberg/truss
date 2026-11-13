type cleanup =
  | Drop_value of Lir.place
  | Free_pointed of Lir.place
  | Free_blocks of { place : Lir.place; variants : string list }
  | Write_back of { destination : Lir.place; source : Lir.place; ty : Ground.ty }
  | Finish_lend of Lir.statement
  | Join_group of Lir.statement

type scope_kind = Bindings | Statement
type scope = { kind : scope_kind; mutable owned : cleanup list }
type loop = { continue_ : Lir.block; continue_depth : int; break_ : Lir.block; break_depth : int }

type frame = {
  code : Definitions.code;
  mutable self_place : Lir.place option;
  exit : (Lir.block * int) option;
  mir : mir_frame option;
}

and mir_frame = {
  body : Mir.body;
  lambdas : Mir.body array;
  places : (Mir.local, Lir.place) Hashtbl.t;
  ends : (Mir.local, cleanup list) Hashtbl.t;
  conditionally_lent : Mir.local list;
  mutable lent : (Mir.local, Lir.local) Hashtbl.t;
  aliases : (Mir.local, int) Hashtbl.t;
  owner : scope option;
  returns_into : Lir.place option;
  forks : (int, int) Hashtbl.t;
  mutable provides : (Path.t * Lir.operand) list list;
  returned : Mir.local list;
  mutable taken : Mir.place list;
}

type early_exits = {
  winner : Lir.place;
  mutable return_value : Lir.place option;
  scope : scope;
  mutable exits : early_exit list;
}

and early_exit = {
  ends : Mir.statement list;
  remaining : (Core.task * Mir.statement list) list;
  exit : Mir.task_exit;
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
type form = Ordinary | Pulled | Looped of { body : Ground.function_type; chunked : bool }

type state = {
  context : Definitions.context;
  mutable frame : frame;
  builder : Lir_builder.t;
  mutable scopes : scope list;
  mutable loops : loop list;
  mutable result : result_slot;
  nested : Lir.function_ option list ref;
  mutable evidence : (Path.t * Lir.operand) list;
  form : form;
  mutable forks : int;
  mutable tasks : task list;
  mutable next_range : schedule;
  mutable caller_site : Lir.local option;
  mutable active_loops : int list;
}

val frame_of : Definitions.code -> frame

val enter :
  Definitions.context -> ?form:form -> ?nested:Lir.function_ option list ref -> frame -> state

val is_pulled : state -> bool
val reports_at_caller : Path.t -> bool
val report_at_caller : Lir.local -> Lir.function_ -> Lir.function_
val caller_site_operand : state -> Lir.site -> Lir.operand
val may_fork : state -> bool
val fresh_fork : state -> int
val new_early_exits : state -> early_exits
val ground : state -> Types.ty -> Ground.ty
val trivial : state -> Ground.ty -> bool
val is_zero_size : state -> Ground.ty -> bool
val site : state -> Syntax.span -> Lir.site

type unsupported = { construct : string; at : Lir.site option }

exception Unsupported of unsupported

val unsupported : ?at:Lir.site -> ('a, unit, string, 'b) format4 -> 'a
val source : state -> Syntax.span -> string
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
val place_type : state -> Lir.place -> Lir.ty option
val lent_at : state -> Lir.place -> Ground.lent option
val project : state -> Lir.place -> Lir.projection -> Lir.place
val constant_int : Memory_layout.integer -> Z.t -> Lir.operand
val scalar_of : state -> Ground.ty -> Memory_layout.scalar
