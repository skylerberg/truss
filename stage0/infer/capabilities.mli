module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls

type checking = {
  state : State.state;
  spans : Syntax.span array;
  mutable provides : (Types.capability list * Core.implementation list * Core.block) list;
}

type scope_kind = Function_body | Lambda_body of Core.origin | Restricted of string

type scope = {
  available : Types.capability list;
  kind : scope_kind;
  implemented_capability : Types.capability option;
}

val check : State.state -> State.Environment.lowered_interface -> Core.t -> unit
