(* The rules of moves. Whether a place can be moved depends on the place and
   on how its root is bound, so the refusals need no dataflow. The move
   analysis that code generation drops by says what may hold a value at
   each point of a body's MIR, from which the checks prevent a use after
   move, and a [mut] borrow that ends with a place of its owner's moved
   out. *)

type verdict = Moves | Reads | Refused of (Context.context -> Syntax.span -> Types.ty -> unit)

val verdict :
  Context.context -> Place.t -> type_:Types.ty -> returned:bool -> captured:bool -> verdict

(* Reports each move the graph makes that its place's root forbids. *)
val check_refused : Context.context -> Graph.t -> unit

(* Checks a definition's MIR. [returns] says whether its body returns to a
   caller, as a function's does. *)
val check : Context.context -> Mir.t -> returns:bool -> unit
