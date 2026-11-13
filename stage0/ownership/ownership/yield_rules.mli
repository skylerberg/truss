type count = Zero | One | Many

val check_yields_once : Context.context -> Mir.body -> name:Syntax.span -> unit

type pulling = Pullable | Yields_mut | Recursive | Yields_places

val pullable : (Path.t, pulling) Query.query
val check_cursors : Context.context -> Mir.t -> unit

val check_concurrent_loops :
  Context.context -> task_hazard:(Path.t -> Views.task_hazard option option) -> Mir.t -> unit
