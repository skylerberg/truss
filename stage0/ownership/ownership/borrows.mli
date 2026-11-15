(* Checks the loans and views of a definition's body, then of each of its
   lambdas', with the move analysis of each body. [returns] says whether the definition's body returns to a
   caller. *)
val check :
  Context.context -> moves:(Mir.Graph.body -> Moves.t) -> returns:bool -> Mir.Graph.t -> unit
