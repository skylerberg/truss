(** Which places of a MIR body may hold a value at each point, and which may hold nothing: a forward
    analysis of the places that are moved out of, given values, and ended. A place is tracked as a
    move path: a local that owns its value, and the fields after it.

    The MIR says what moves:
    - A call moves each argument passed to an [own] parameter. A value lent to a read-only or [mut]
      parameter stays the caller's, whose end drops it.
    - An assignment moves each value it reads by value: the operand it assigns, a constructor's
      fields, an array's elements, an operation's operands, and the value made [any].
    - A [return], and a [yield], move the values they give.
    - A loop that pulls values gives its part one at the start of each iteration.

    Code generation drops a path where its local ends, by what holds there: all of it, the parts
    that were not moved out, or, where it may or may not hold a value, what a flag says. *)

type step = Field of string | Variant of { variant : string; field : string }
type path = { local : Mir.local; steps : step list }

val path_of_place : Mir.place -> path option
(** [None] for a constant's static data, which nothing moves from. *)

val is_inside : outer:path -> path -> bool
(** Whether a path is [outer] or lies inside it. *)

type t

val analyse :
  ?passed:(Mir.local -> Types.mode option) ->
  ?moving:(Types.ty -> bool) ->
  tracks:(path -> bool) ->
  Mir.body ->
  t
(** The analysis of a body. A local owns its value where it is a temporary or an [own] binding, and
    not a capture or a local that an assignment gives a place; its parameters hold values on entry.
    A local bound [mut], or lent [mut], is another owner's place lent [mut]: a value may be moved
    out of one, which is reinitialized before the local ends, and none is dropped where it ends.
    [passed] says how a parameter is passed where its binding does not, as for a lambda's. A value
    read by value moves where [moving] holds of its type, every value by default; the rest copy. A
    path is tracked where [tracks] holds of it. *)

val owns : t -> Mir.local -> bool
(** Whether a local owns its value, which its end drops. *)

val lent_mut : t -> Mir.local -> bool
(** Whether a local is another owner's place lent [mut]. *)

val places_given : t -> Mir.local -> int
(** How many assignments give a local a place, so that it holds no value of its own. *)

val built_values : t -> Mir.local -> Mir.rvalue list option
(** For a lent local that some assignment constructs around places, the values assigned to it. *)

type use = {
  place : Mir.place;
  origin : Core.origin;
  moves : bool;
  operand : Mir.operand option;  (** The operand that reads the place, if one does *)
  passed : Types.mode option;  (** For an argument, the mode of the parameter it is passed to *)
}
(** A place code reads, where it reads it, and whether the read moves the value out. *)

val statement_uses : t -> Mir.statement -> use list
(** The places a statement reads, in evaluation order. A place it gives a value is not among them.
*)

val terminator_uses : t -> Mir.basic_block -> use list
(** The places a block's terminator reads, in evaluation order. *)

val given_by : Mir.statement -> path list
(** The places a statement gives values. *)

val ended_by : Mir.statement -> Mir.local list
(** The locals a statement ends. *)

type state

val entry : t -> Mir.block -> state
(** The state where a block starts, which the caller may change. *)

val apply : t -> state -> Mir.statement -> unit
(** Runs a statement's effects. *)

val apply_moves : t -> state -> Mir.statement -> unit
(** Runs a statement's moves alone, which happen before it gives its destination a value. *)

val apply_terminator_moves : t -> state -> Mir.basic_block -> unit
(** Runs the moves a block's terminator makes before it leaves its block. The ends an exit from
    tasks runs are statements of their own, which run where the exit is taken. *)

val copy : state -> state

val move_out : t -> state -> Mir.place -> origin:Core.origin -> unit
(** Moves the value at a place out, as one of a statement's reads at [origin] does. *)

val moved_at : t -> state -> path -> Core.origin list
(** Where the moves are that may have left a tracked path empty. *)

type status = Holds | Empty | Maybe

val status : t -> state -> path -> status option
(** [None] for a path that is not tracked, which holds a value whenever its local does. *)

val may_be_empty : t -> state -> path -> path option
(** The outermost tracked path that overlaps a path, around it or inside it, and may hold nothing,
    because it was moved out of or not yet given a value on some path here. *)

val inside : t -> path -> path list
(** The tracked paths strictly inside a path, outermost first. *)

val flagged : t -> path list
(** The paths that may or may not hold a value where they are dropped, which a run-time flag
    follows. *)

val changed : t -> before:state -> after:state -> (path * bool) list
(** The flagged paths whose flag a step from [before] to [after] changes, each with its new value.
*)

val held_at_entry : t -> path list
(** The flagged paths that hold a value on entry: the parameters'. *)

val given_on_entry : t -> Mir.block -> path list
val kept_by_cursor : t -> Mir.body -> Mir.local list
