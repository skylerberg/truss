type loop = Outside | Inside | Across_lambda | Parallel_body | Branch

type context = {
  specification : bool;
  assert_allowed : bool;
  function_body : bool;
  in_yielding_method : bool;
  loop : loop;
  in_parallel : bool;
  in_task : bool;
}

val signature : Cursor.t -> Syntax.signature -> unit
val definition : Cursor.t -> Syntax.definition -> unit
