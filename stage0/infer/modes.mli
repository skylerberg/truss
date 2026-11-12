(** What a call lends, which places may be mutated, and whether each argument is passed in the mode
    its parameter takes. *)

open State
module T = Types

val note_lending : state -> Syntax.expression -> T.result -> unit
val lent : state -> Syntax.expression -> T.mode option
val borrowed : state -> Syntax.expression -> bool
val scrutinee_mode : state -> Syntax.expression -> T.mode

type immutable = Read_only of string | Captured of string | Lent_read_only | Not_a_place
type mutation = Assignment | Mut_mark

val mutate : state -> env -> by:mutation -> Syntax.expression -> unit

type argument_form = Marked of T.mode * Syntax.expression | Place | Lent of T.mode | Temporary

val lent_field : state -> Syntax.expression -> Unify.T.ty -> T.mode option
val check_mode : state -> env -> Syntax.expression -> T.parameter_info -> Unify.T.ty -> unit
val check_lent_value : state -> env -> Syntax.expression -> unit
val check_owned : state -> env -> Syntax.expression -> Unify.T.ty -> unit
