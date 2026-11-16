type path = { local : Mir.local; projections : Mir.projection list }

val path_of_place : Mir.place -> path option
val is_inside : outer:path -> path -> bool

type t

val analyse :
  ?find_passed:(Mir.local -> Types.mode option) ->
  ?is_moving:(Types.ty -> bool) ->
  tracks:(path -> bool) ->
  Mir.Graph.body ->
  t

val owns : t -> Mir.local -> bool
val is_lent_mut : t -> Mir.local -> bool

type use = {
  place : Mir.place;
  origin : Core.origin;
  moves : bool;
  operand : Mir.operand option;
  passed : Types.mode option;
}

val list_statement_uses : t -> Mir.Graph.statement -> use list
val list_terminator_uses : t -> Mir.Graph.basic_block -> use list
val list_given_by : Mir.Graph.statement -> path list
val list_ended : Mir.Graph.statement -> Mir.local list

type state

val copy_entry_state : t -> Mir.Graph.block -> state
val apply : t -> state -> Mir.Graph.statement -> unit
val apply_moves : t -> state -> Mir.Graph.statement -> unit
val apply_terminator_moves : t -> state -> Mir.Graph.basic_block -> unit
val copy : state -> state
val move_out : t -> state -> Mir.place -> origin:Core.origin -> unit
val list_moved_at : t -> state -> path -> Core.origin list

type status = Holds | Empty | Maybe

val find_status : t -> state -> path -> status option
val find_possibly_empty : t -> state -> path -> path option
val list_inside : t -> path -> path list
val list_flagged : t -> path list
val list_changed : t -> before:state -> after:state -> (path * bool) list
val list_held_at_entry : t -> path list
val list_given_on_entry : t -> Mir.Graph.block -> path list
val compute_live_after : t -> Mir.Graph.body -> Mir.Graph.block -> int -> Mir.local -> bool
