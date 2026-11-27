type arc = { source : int; target : int; is_strict : bool }
type graph = arc list

type site = {
  origin : Core.origin;
  target : Path.t;
  graphs : graph list;
  passage : Catalog.Prover.passage;
}

type summary = { sites : site list; ranked_parameters : int list }

val summarize : Call_edges.lookups -> Path.t -> summary

type occurrence = Absent | Whole | Within | Consumed | Out_of_reach of Types.ty

val classify_holding : Interface.Lookups.t -> heads:Path.t list -> Types.ty -> occurrence
val holds_itself : Interface.Lookups.t -> Types.ty -> bool
val find_value_maker : Call_edges.lookups -> Types.generic list -> Types.parameter -> Path.t option

type call = {
  caller : Path.t;
  origin : Core.origin;
  callee : Path.t;
  passage : Catalog.Prover.passage;
}

type component = Level of int | Largest_rank of int list

type verdict = {
  calls_without_decrease : call list;
  ranking : (Path.t * component list) list option;
}

val decide : (Path.t * summary) list -> (Path.t * verdict) list
