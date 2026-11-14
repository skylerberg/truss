(* Why a task that starts at one of a method's [yield]s cannot keep the
   yielded value after the method resumes. *)
type task_hazard = Yields_mut | Borrows of string

(* Checks the loans and views of a definition's MIR, with the move analysis
   of each body. [returns] says whether the definition's body returns to a
   caller. Gives the task hazard of the definition's [yield]s, if it has
   one. *)
val check :
  Context.context -> moves:(Mir.body -> Moves.t) -> returns:bool -> Mir.t -> task_hazard option
