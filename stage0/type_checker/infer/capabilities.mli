type checking = {
  state : State.state;
  mutable provides : (Types.capability_set * Core.implementation list * Core.block) list;
}

type scope_kind = Function_body | Lambda_body of Core.origin | Restricted of string

type scope = {
  available : Types.capability_set;
  kind : scope_kind;
  implemented_capability : Types.capability option;
}

val check : State.state -> Interface.Environment.elaborated_interface -> Core.t -> unit
