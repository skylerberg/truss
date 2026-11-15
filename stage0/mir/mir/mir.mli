include module type of struct
  include Tree
end

module Graph = Graph
module Call_edges = Call_edges

include module type of struct
  include Walk
end

include module type of struct
  include Parts
end

val code_of_formula : formula -> Graph.t
val body_part : ?interface:Interface.Environment.interface -> Core.t -> body_part

val contract_part :
  type_interface:(Path.t -> Types.type_interface option) -> Path.t -> Core.t -> contract_part

module For_testing : sig
  val expanded : t -> Graph.t
end
