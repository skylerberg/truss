module T = Types

type verdict = Moves | Reads | Refused of (Context.context -> Syntax.span -> Context.T.ty -> unit)

val verdict :
  Context.context -> Place.t -> type_:Types.ty -> returned:bool -> captured:bool -> verdict

type moved = Place.t * int

val check : Context.context -> Graph.t -> unit
