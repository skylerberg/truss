type held_views = (Place.root * Actions.view list) list
type task_hazard = Yields_mut | Borrows of string

val check : Context.context -> Actions.t -> task_hazard option
