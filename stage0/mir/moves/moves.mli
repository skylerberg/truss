type step = Field of string | Variant of { variant : string; field : string }
type path = { local : Mir.local; steps : step list }

val path_of_place : Mir.place -> path option
val is_inside : outer:path -> path -> bool

type t

val analyse :
  ?passed:(Mir.local -> Types.mode option) ->
  ?moving:(Types.ty -> bool) ->
  tracks:(path -> bool) ->
  Mir.Graph.body ->
  t

val owns : t -> Mir.local -> bool
val lent_mut : t -> Mir.local -> bool

type use = {
  place : Mir.place;
  origin : Core.origin;
  moves : bool;
  operand : Mir.operand option;
  passed : Types.mode option;
}

val statement_uses : t -> Mir.Graph.statement -> use list
val terminator_uses : t -> Mir.Graph.basic_block -> use list
val given_by : Mir.Graph.statement -> path list
val ended_by : Mir.Graph.statement -> Mir.local list

type state

val entry : t -> Mir.Graph.block -> state
val apply : t -> state -> Mir.Graph.statement -> unit
val apply_moves : t -> state -> Mir.Graph.statement -> unit
val apply_terminator_moves : t -> state -> Mir.Graph.basic_block -> unit
val copy : state -> state
val move_out : t -> state -> Mir.place -> origin:Core.origin -> unit
val moved_at : t -> state -> path -> Core.origin list

type status = Holds | Empty | Maybe

val status : t -> state -> path -> status option
val may_be_empty : t -> state -> path -> path option
val inside : t -> path -> path list
val flagged : t -> path list
val changed : t -> before:state -> after:state -> (path * bool) list
val held_at_entry : t -> path list
val given_on_entry : t -> Mir.Graph.block -> path list
val live_after : t -> Mir.Graph.body -> Mir.Graph.block -> int -> Mir.local -> bool
