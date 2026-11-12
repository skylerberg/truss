module T = Types

type held_views = (Place.root * Graph.view list) list
type task_hazard = Yields_mut | Borrows of string

val check : Context.context -> Graph.t -> task_hazard option
