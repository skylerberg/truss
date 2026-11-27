type arc = { source : int; target : int; is_strict : bool }
type graph = arc list

type site = {
  origin : Core.origin;
  target : Path.t;
  graphs : graph list;
  passage : Catalog.Prover.passage;
}

val list_sites : Call_edges.lookups -> Path.t -> site list

type call = {
  caller : Path.t;
  origin : Core.origin;
  callee : Path.t;
  passage : Catalog.Prover.passage;
}

val list_calls_without_decrease : (Path.t * site list) list -> call list
val decreases_lexicographically : positions:int list -> graph -> bool
