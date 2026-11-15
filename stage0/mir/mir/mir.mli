include module type of struct
  include Tree
end

module Graph = Graph

include module type of struct
  include Walk
end

val code_of_formula : formula -> Graph.t
val is_lowered : Query.context -> Resolve.Names.key -> bool
val mir : (Resolve.Names.key, t option) Query.query
val of_path : (Path.t, t option) Query.query
val graph : (Resolve.Names.key, Graph.t option) Query.query
val graph_of_path : (Path.t, Graph.t option) Query.query
val defaults_of_path : (Path.t, t defaults option) Query.query
val default_graphs_of_path : (Path.t, Graph.t defaults option) Query.query
val contract_of_path : (Path.t, contract option) Query.query
val laws : (Resolve.Names.key, law list) Query.query
val type_clauses_of_path : (Path.t, type_clauses option) Query.query
val is_generated : Query.context -> Path.t -> bool
val of_constant : (Path.t, t option) Query.query
val graph_of_constant : (Path.t, Graph.t option) Query.query

module For_testing : sig
  val expanded : t -> Graph.t
end
