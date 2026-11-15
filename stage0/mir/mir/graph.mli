open Tree

type block = int
type early_exit = { resume : block; returned : local option }
type branch = { entry : block; blocks : block list }

type terminator =
  | Goto of block
  | Branch of { condition : operand; yes : block; no : block; is_if_condition : bool }
  | For of {
      iteration : iteration;
      part : local;
      lent : lent_element option;
      body : block;
      binding_count : int;
      blocks : block list;
      after : block;
      loop : loop;
    }
  | Fork of { fork : Core.origin; concurrent : bool; branches : branch list; join : block option }
  | Join of { fork : Core.origin; next : block }
  | Iteration_end of { loop : block }
  | Yield of { mode : Types.mode; part : yielded; resume : block }
  | Return of operand option
  | Cancel of {
      task : task;
      task_end : block option;
      winner : local;
      number : int;
      returned : (operand * local) option;
    }
  | Resume of { winner : local; exits : early_exit list; next : block }
  | Unreachable
  | Written_unreachable
  | Todo

type basic_block = {
  statements : statement list;
  terminator : terminator;
  terminator_origin : Core.origin;
}

type body = {
  parameters : local list;
  captures : local list;
  locals : local_info array;
  blocks : basic_block array;
}

type t = { body : body; lambdas : body array }

val canonical : basic_block array -> basic_block array
val successors : terminator -> block list
val iteration_loop : terminator -> block option
val block_successors : body -> block -> block list
