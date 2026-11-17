type static_ =
  | Static_type of Types.ty
  | Static_trait of Path.t * Types.argument list option
  | Static_capability of Path.t

val require :
  State.state ->
  at:Source.Definition_span.t ->
  Types.ty ->
  Types.trait_reference ->
  on_unmet:(Types.ty -> (string * Types.ty) option -> unit) ->
  unit

val make_fresh_generic_arguments : State.state -> Types.generic list -> Types.argument list
val make_fresh_arguments : State.state -> Path.t -> Types.argument list
val make_fresh_trait_reference : State.state -> Path.t -> Types.trait_reference
val instantiate_type : State.state -> Source.Definition_span.t -> Path.t -> Types.argument list
val find_static : State.state -> Syntax.expression -> static_ option

val check_named_type :
  State.state -> Syntax.expression -> Path.t -> Syntax.bracket_item list option -> Types.ty

val check_written_arguments :
  State.state -> Syntax.bracket_item list -> (Types.argument list, Types.ty) result

type instance = {
  signature : Types.signature;
  substitution : Types.substitution;
  type_arguments : Types.argument list;
  capability_arguments : Types.capability_set list;
}

val instantiate :
  State.state ->
  Source.Definition_span.t ->
  ?extra:Types.substitution ->
  Types.signature ->
  instance

val find_function_signature : State.state -> Path.t -> Types.signature option
