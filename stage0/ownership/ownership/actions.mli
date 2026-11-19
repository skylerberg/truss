type view = Borrow_of of Place.t | Copy_of_view_in of Place.t

val extract_viewed_place : view -> Place.t

type loan = { borrowed : Place.t; mode : Types.mode; duration : Mir.loan_duration }

type borrowed_argument = {
  place : Place.t;
  mode : Types.mode;
  origin : Core.origin;
  position : int;
}

type view_argument = { position : int; views : view list; origin : Core.origin }
type dropped_owner = { owner : Place.root; origin : Core.origin }

type action =
  | Read of Place.t
  | Move of { place : Place.t; type_ : Types.ty; is_returned : bool; is_captured : bool }
  | Move_out_of_lent of Types.ty
  | Mutate of Place.t
  | Assign of Place.t
  | Bind of Core.local list
  | Yield_point of { views : view list; parts : Place.t list; forwarded : view list }
  | Bind_views of { locals : Core.local list; views : view list }
  | Store of { place : Place.t; views : view list; replaces_root : bool }
  | Return_view of view list
  | Drop of dropped_owner list
  | Bind_lent_part of { scrutinee : Core.origin; lent_part_type : Types.ty }
  | Pass_owned_function of view list
  | Start_loan of { loan : int; loans : loan list }
  | End_loans of int list
  | Write_through of Place.t
  | Arguments of {
      borrowed_arguments : borrowed_argument list;
      view_arguments : view_argument list;
      is_yielded : bool;
    }

type position = { block : Mir.Graph.block; index : int }
type step = { action : action; origin : Core.origin }
type fork_join_block = { keyword : string; branches : position list list }

type fork_join_loop = {
  keyword : string;
  body : position list;
  pattern_locals : Core.local list;
  temporaries : Mir.local list;
}

type t = {
  body : Mir.Graph.body;
  steps : step list array array;
  fork_join_blocks : fork_join_block list;
  fork_join_loops : fork_join_loop list;
}

val of_body : Context.context -> Moves.t -> Mir.Graph.body -> returns_to_caller:bool -> t
