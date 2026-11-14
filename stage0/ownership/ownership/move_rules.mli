(* The rules of moves. Whether a place can be moved depends on the place and
   on how its root is bound, so the refusals need no dataflow. The move
   analysis that code generation drops by says what may hold a value at
   each point of a body's MIR, from which the checks prevent a use after
   move, and a [mut] borrow that ends with a place of its owner's moved
   out. *)

type verdict = Moves | Reads | Refused of (Context.context -> Syntax.span -> Types.ty -> unit)

val verdict :
  Context.context -> Place.t -> type_:Types.ty -> returned:bool -> captured:bool -> verdict

(* Reports each move a body's actions make that its place's root forbids. *)
val check_refused : Context.context -> Actions.t -> unit

(* The move analysis of a body: a value whose type is not plain moves where
   it is read by value. *)
val analyse : Context.context -> Mir.body -> Moves.t

(* Checks a definition's MIR, with the move analysis of each body. [returns]
   says whether its body returns to a caller, as a function's does. *)
val check : Context.context -> Mir.t -> moves:(Mir.body -> Moves.t) -> returns:bool -> unit
