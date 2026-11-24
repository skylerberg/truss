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

val find_local_name : Core.local -> string option

val list_callee_modified_fields :
  read_signature:(Path.t -> Types.signature option) ->
  Interface.Lookups.t ->
  Types.substitution ->
  callee ->
  int ->
  string list list option

val expand_formula : formula -> Graph.t
val make_body_part : ?interface:Interface.Environment.interface -> Core.t -> body_part

val make_contract_part :
  find_type_interface:(Path.t -> Types.type_interface option) -> Path.t -> Core.t -> contract_part

val expand : t -> Graph.t
