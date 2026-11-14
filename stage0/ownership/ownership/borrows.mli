(* Checks the loans and views of a definition's MIR, with the move analysis
   of each body. [returns] says whether the definition's body returns to a
   caller. *)
val check : Context.context -> moves:(Mir.body -> Moves.t) -> returns:bool -> Mir.t -> unit
