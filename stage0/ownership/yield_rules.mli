type count = Zero | One | Many

val check_yields_once : Context.context -> Core.block -> name:Syntax.span -> unit

type pulling = Pullable | Yields_mut | Recursive | Yields_places

val pullable : (Path.t, pulling) Query.query
val check_cursors : Context.context -> Core.definition -> unit

val check_concurrent_loops :
  Context.context ->
  task_hazard:(Path.t -> Views.task_hazard option option) ->
  Core.definition ->
  unit
