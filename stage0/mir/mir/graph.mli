type block = int
type early_exit = { resume : block; returned : Tree.local option }
type branch = { entry : block; blocks : block list }

type statement_kind =
  | Basic of Tree.basic
  | Provide_start of { provided : Tree.provided list; can_use_tasks : bool }
  | Provide_end

type statement = { kind : statement_kind; origin : Core.origin }

type loop_head = {
  iteration : Tree.iteration;
  part : Tree.local;
  elements : Tree.elements option;
  body : block;
  blocks : block list;
  after : block;
  loop : Tree.loop;
}

type terminator =
  | Goto of block
  | Branch of { condition : Tree.operand; yes : block; no : block }
  | For of loop_head
  | Fork of { fork : Core.id; concurrent : bool; branches : branch list; join : block option }
  | Join of { fork : Core.id; next : block }
  | Iteration_end of { loop : block }
  | Yield of { mode : Language.Mode.t; part : Tree.yielded; resume : block }
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

val canonicalize : basic_block option array -> basic_block array
val find_iteration_loop : terminator -> block option
val read_loop_head : body -> block -> loop_head
val list_block_successors : body -> block -> block list

module For_testing : sig
  val list_successors : terminator -> block list
end
