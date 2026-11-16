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

val expand_formula : formula -> Graph.t
val make_body_part : ?interface:Interface.Environment.interface -> Core.t -> body_part

val make_contract_part :
  type_interface:(Path.t -> Types.type_interface option) -> Path.t -> Core.t -> contract_part

module For_testing : sig
  val expand : t -> Graph.t
end
