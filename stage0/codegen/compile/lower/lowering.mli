type cleanup =
  | Drop_value of Lowered.place
  | Drop_flagged of { place : Lowered.place; flag : Lowered.place }
  | Free_pointed of Lowered.place
  | Free_blocks of { place : Lowered.place; variants : string list }
  | Write_back of { destination : Lowered.place; source : Lowered.place; ty : Ground.ty }
  | Join_group of Lowered.statement

type scope_kind = Bindings | Statement
type scope = { kind : scope_kind; mutable owned : cleanup list }

type loop = {
  continue_ : Lowered.block;
  continue_depth : int;
  break_ : Lowered.block;
  break_depth : int;
}

type frame = {
  code : Definitions.code;
  mutable self_place : Lowered.place option;
  inlined : Path.t list;
  reported : Lowered.site option;
  exit : (Lowered.block * int) option;
  mir : mir_frame option;
}

and mir_frame = {
  body : Mir.body;
  lambdas : Mir.body array;
  places : (Mir.local, Lowered.place) Hashtbl.t;
  owner : scope option;
  returns_into : Lowered.place option;
  mutable provides : (Path.t * Lowered.operand) list list;
  returned : Mir.local list;
  mutable taken : Mir.place list;
  moves : Moves.t;  (** Which places may hold a value at each point *)
  flags : (Moves.path * Lowered.place) list;
      (** The [Bool] local that says whether each flagged path holds a value *)
  mutable state : Moves.state;
  lent_slot : (Lowered.place * Ground.ty) option;
      (** In a lending method compiled as a function, the slot of the caller's where the method
          builds a part that is not a place of its parameters, and the part's type *)
  called_lends : (Mir.local, bool) Hashtbl.t;
      (** Each part that a call of a lending function lends, and whether that call was given
          [lent_slot] as its own slot *)
}

type task = { id : Core.task; group : Lowered.place; end_block : Lowered.block; scope_depth : int }

type spawn_loop = {
  origin : Core.origin;
  group : Lowered.place;
  item : Lowered.local;
  element : Ground.ty;
}

type schedule = Sequential | Chunked | Spawned of spawn_loop
type result_slot = Through of Lowered.local | Returned_in of Lowered.local | No_result

type state = {
  context : Definitions.context;
  mutable frame : frame;
  builder : Emit_c.Builder.t;
  mutable scopes : scope list;
  mutable loops : loop list;
  mutable result : result_slot;
  nested : int ref;
  mutable evidence : (Path.t * Lowered.operand) list;
  mutable tasks : task list;
  mutable moved : Lowered.place list;
}

val frame_of : Definitions.code -> inlined:Path.t list -> frame
val enter : Definitions.context -> ?nested:int ref -> builder:Emit_c.Builder.t -> frame -> state
val may_fork : state -> bool

(* A new local, as the place that holds a value. *)
val held : state -> ?name:string -> Lowered.ty -> Lowered.place

(* Writes code with [body] as an outlined function, nested in the instance,
   given [parts] as its parameters. Gives the function's number and the
   operand for its environment. *)
val outlined : state -> parts:Lowered.local list -> (unit -> unit) -> int * Lowered.operand
val ground : state -> Types.ty -> Ground.ty
val trivial : state -> Ground.ty -> bool
val is_zero_size : state -> Ground.ty -> bool
val site : state -> Syntax.span -> Lowered.site

type unsupported = { construct : string; at : Lowered.site option }

exception Unsupported of unsupported

val unsupported : ?at:Lowered.site -> ('a, unit, string, 'b) format4 -> 'a
val source : state -> Syntax.span -> string
val innermost_scope : state -> scope
val temporary : state -> ?name:string -> Ground.ty -> Lowered.place
val binding : state -> ?name:string -> Ground.ty -> Lowered.place

val flagged_binding : state -> Ground.ty -> flag:Lowered.place -> Lowered.place
(** A [binding] that only some paths initialize, whose value is dropped where its drop flag, the
    [Bool] at [flag], is true. *)

val parameter :
  state ->
  ?how:(Ground.mode -> Ground.ty -> Lowered.ty option) ->
  ?in_scope:bool ->
  owned:bool ->
  Ground.mode ->
  Ground.ty ->
  Lowered.local option * Lowered.place

val evidence_parameters : state -> Path.t list -> Lowered.local list
val result_slot : state -> Convention.result -> unit
val result_place : state -> Lowered.place option
val return_result : state -> Lowered.terminator
val leave_to : state -> int -> unit
val open_scope : state -> scope_kind -> scope
val close_scope : state -> scope -> unit
val in_scope : state -> (unit -> 'a) -> 'a
val in_statement : state -> (unit -> 'a) -> 'a

val finish_function :
  state -> ?returns:bool -> first:Lowered.local list -> rest:Lowered.local list -> unit -> unit

val finish_instance :
  state -> ?returns:bool -> rest:Lowered.local list -> unit -> Emit_c.Builder.instance

val unreachable_block : state -> unit
val moved : state -> Lowered.place -> Lowered.operand
val owned : state -> Lowered.place -> Ground.ty -> Lowered.operand
val take : state -> Lowered.place -> Ground.ty -> destination:Lowered.place -> unit
val snapshot : state -> Lowered.place -> Lowered.place

val looping :
  state -> continue_:Lowered.block -> break_:Lowered.block -> depth:int -> (unit -> unit) -> unit

val place_type : state -> Lowered.place -> Lowered.ty option
val lent_at : state -> Lowered.place -> Ground.lent option
val project : state -> Lowered.place -> Lowered.projection -> Lowered.place
val constant_int : Memory_layout.integer -> Z.t -> Lowered.operand
val scalar_of : state -> Ground.ty -> Memory_layout.scalar
