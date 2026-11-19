type static_ =
  | Static_type of Types.ty
  | Static_trait of Path.t * Types.argument list option
  | Static_capability of Path.t

val check_grants_when_final :
  State.state -> Source.Definition_span.t -> Types.ty -> Types.trait_reference -> unit

val make_fresh_arguments : State.state -> Path.t -> Types.argument list
val make_fresh_trait_reference : State.state -> Path.t -> Types.trait_reference
val instantiate_type : State.state -> Source.Definition_span.t -> Path.t -> Types.argument list
val find_static : State.state -> Syntax.expression -> static_ option

val check_named_type :
  State.state -> Syntax.expression -> Path.t -> Syntax.bracket_item list option -> Types.ty

val check_written_arguments :
  State.state -> Syntax.bracket_item list -> (Types.argument list, Types.ty) result

type instance = {
  declared : Types.signature;
  signature : Types.signature;
  substitution : Types.substitution;
  instantiation : Types.instantiation;
  flatten : Types.ty -> Types.ty;
}

val instantiate :
  State.state ->
  Source.Definition_span.t ->
  ?extra:Types.substitution ->
  Types.signature ->
  instance

val find_function_signature : State.state -> Path.t -> Types.signature option
