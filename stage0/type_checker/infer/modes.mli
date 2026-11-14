(** A call's lent places, which places may be mutated, and whether each argument is passed in the
    mode its parameter takes. *)

open State

val note_lending : state -> Syntax.expression -> Types.result -> unit
val lent : state -> Syntax.expression -> Types.mode option
val borrowed : state -> Syntax.expression -> bool
val scrutinee_mode : state -> Syntax.expression -> Types.mode

type immutable = Read_only of string | Captured of string | Lent_read_only | Not_a_place
type mutation = Assignment | Passed_mut

val mutate : state -> env -> by:mutation -> Syntax.expression -> unit

type argument_form =
  | With_mode of Types.mode * Syntax.expression
  | Place
  | Lent of Types.mode
  | Temporary

val lent_field : state -> Syntax.expression -> Types.ty -> Types.mode option
val check_mode : state -> env -> Syntax.expression -> Types.parameter_info -> Types.ty -> unit
val check_lent_value : state -> env -> Syntax.expression -> unit
val check_owned : state -> env -> Syntax.expression -> Types.ty -> unit
