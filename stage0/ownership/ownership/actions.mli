(* The ownership actions of a definition's MIR: for each statement and
   terminator of each body, what it does to the places, loans, and views the
   checks follow. *)

(* A loan: a borrow of a place that lasts for a region of code. While a
   read-only loan is live, the place cannot be mutated. While a [mut] loan
   is live, the place cannot be used at all. *)
type duration = Loop_body | Provide_body | Rest_of_statement | Operand_evaluation
type loan = { borrowed : Place.t; mode : Types.mode; duration : duration }

(* A place that a view-typed value may borrow from: the place itself, or,
   [copied_out], the views a view stored in it borrows. *)
type view = { place : Place.t; copied_out : bool }

(* An argument that is a place: the place, the parameter's mode, the
   argument's origin, and its position in the argument list. *)
type borrowed_argument = { place : Place.t; mode : Types.mode; at : Core.origin; position : int }

type action =
  | Read of Place.t
  | Move of { place : Place.t; type_ : Types.ty; returned : bool; captured : bool }
  | Move_out_of_lent of Types.ty
  | Mutate of Place.t
  | Assign of Place.t
  | Bind of Core.local list
  | Yield_point of { mode : Types.mode; lent : Place.t option list; views : view list }
  | Bind_views of { locals : Core.local list; views : view list }
  | Store of { place : Place.t; views : view list }
  | Return_view of view list
  | View_of_temporary of Place.t option
  | Bind_lent_part of Types.ty
  | Pass_owned_function of view list
  | Start_loan of { loan : int; loans : loan list }
  | End_loans of int list
  | Write_through of Place.t
  | Arguments of {
      places : borrowed_argument list;
      views : (int * view list * Core.origin) list;
      yielded : bool;
    }

(* A position in a block: one of its statements, then the ends an exit from
   tasks runs on its way out, then its terminator. *)
type position = { block : Mir.block; index : int }
type step = { action : action; origin : Core.origin }
type fork_join_block = { keyword : string; branches : position list list }
type fork_join_loop = { keyword : string; body : position list; bound : Core.local list }

type t = {
  body : Mir.body;
  steps : step list array array;  (** Each position's actions, in order *)
  fork_join_blocks : fork_join_block list;
  fork_join_loops : fork_join_loop list;
}

(* Where control goes from the end of a block, and, for an exit from tasks,
   where the other tasks of the group go on from before the ends the exit
   runs: each successor, and whether it leaves from before those ends.
   [loops] is [Mir.iteration_loops] of the body. *)
val successors :
  Mir.body -> (Mir.block, Mir.block) Hashtbl.t -> Mir.block -> (Mir.block * bool) list

(* A forward dataflow analysis of a body's actions: the state before each
   action, for each position some path reaches. [join] merges a state into
   a known one, and gives the merged state where the known one grew. *)
val forward :
  t ->
  init:'a ->
  transfer:(step -> 'a -> 'a) ->
  join:('a -> into:'a -> 'a option) ->
  'a array array option array

(* The loans live before each action, oldest first. *)
val live_loans : t -> loan list array array option array

(* The actions of a definition's body, then of each of its lambdas', with
   [moves], the move analysis of each body, giving each statement's reads. *)
val of_mir :
  plain:(Types.ty -> bool) ->
  is_view:(Types.ty -> bool) ->
  holds_function:(Types.ty -> bool) ->
  stores_function:(Mir.callee -> int -> bool) ->
  returns:bool ->
  is_var:(Core.local -> bool) ->
  moves:(Mir.body -> Moves.t) ->
  Mir.t ->
  t list
