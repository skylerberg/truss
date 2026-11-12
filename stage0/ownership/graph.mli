type duration = Loop_body | Provide_body | Rest_of_statement | Operand_evaluation
type loan = { borrowed : Place.t; mode : Types.mode; duration : duration }
type view = { place : Place.t; copied_out : bool }
type borrowed_argument = { place : Place.t; mode : Types.mode; at : Core.origin; position : int }

type action =
  | Enter
  | Read of Place.t
  | Move of { place : Place.t; use : Core.id; type_ : Types.ty; returned : bool; captured : bool }
  | Move_out_of_lent of Types.ty
  | Mutate of Place.t
  | Assign of Place.t
  | Bind of Core.local list
  | Scope_end of Core.local list
  | Task_end of { first : int; limit : int }
  | Yield_point of { mode : Types.mode; lent : Place.t option list; views : view list }
  | Exit
  | Bind_views of { locals : Core.local list; views : view list }
  | Store of { place : Place.t; views : view list }
  | Return_view of view list
  | View_of_temporary of Place.t option
  | Bind_lent_part of Types.ty
  | Pass_owned_function of view list
  | Write_through of Place.t
  | Arguments of {
      places : borrowed_argument list;
      views : (int * view list * Core.origin) list;
      yielded : bool;
    }

type range = { first : int; limit : int }

type point = {
  action : action;
  origin : Core.origin;
  loans : loan list;
  mutable successors : int list;
}

type fork_join_block = { keyword : string; branches : range list }
type fork_join_loop = { keyword : string; body : range; bound : Core.local list }

type t = {
  points : point array;
  entries : int list;
  fork_join_blocks : fork_join_block list;
  fork_join_loops : fork_join_loop list;
}

type builder = {
  table : (int, point) Hashtbl.t;
  mutable count : int;
  mutable entries : int list;
  mutable loops : (int list ref * int list ref) list;
  mutable captured : Core.local list;
  mutable loans : loan list;
  mutable fork_join_blocks : fork_join_block list;
  mutable fork_join_loops : fork_join_loop list;
  plain : Types.ty -> bool;
  is_view : Types.ty -> bool;
  holds_function : Types.ty -> bool;
  stores_function : Core.callee -> int -> bool;
}

val of_definition :
  plain:(Types.ty -> bool) ->
  is_view:(Types.ty -> bool) ->
  holds_function:(Types.ty -> bool) ->
  stores_function:(Core.callee -> int -> bool) ->
  Core.definition ->
  t option
