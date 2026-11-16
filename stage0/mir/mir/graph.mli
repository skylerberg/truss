type block = int
type early_exit = { resume : block; returned : Tree.local option }
type branch = { entry : block; blocks : block list }
type statement = { kind : Tree.basic; origin : Core.origin }

type loop_head = {
  iteration : Tree.iteration;
  part : Tree.local;
  lent : Tree.lent_element option;
  body : block;
  binding_count : int;
  blocks : block list;
  after : block;
  loop : Tree.loop;
}

type terminator =
  | Goto of block
  | Branch of { condition : Tree.operand; yes : block; no : block; is_if_condition : bool }
  | For of loop_head
  | Fork of { fork : Core.origin; concurrent : bool; branches : branch list; join : block option }
  | Join of { fork : Core.origin; next : block }
  | Iteration_end of { loop : block }
  | Yield of { mode : Types.mode; part : Tree.yielded; resume : block }
  | Return of Tree.operand option
  | Cancel of {
      task : Tree.task;
      task_end : block option;
      winner : Tree.local;
      number : int;
      returned : (Tree.operand * Tree.local) option;
    }
  | Resume of { winner : Tree.local; exits : early_exit list; next : block }
  | Unreachable
  | Written_unreachable
  | Todo

type basic_block = {
  statements : statement list;
  terminator : terminator;
  terminator_origin : Core.origin;
}

type body = {
  parameters : Tree.local list;
  captures : Tree.local list;
  locals : Tree.local_info array;
  blocks : basic_block array;
}

type t = { body : body; lambdas : body array }

val canonicalize : basic_block array -> basic_block array
val find_iteration_loop : terminator -> block option
val read_loop_head : body -> block -> loop_head
val list_block_successors : body -> block -> block list

module For_testing : sig
  val successors : terminator -> block list
end
