type static_ =
  | Static_type of Types.ty
  | Static_trait of Path.t * Types.argument list option
  | Static_capability of Path.t

val require :
  State.state ->
  at:Source.Definition_span.t ->
  Types.ty ->
  Types.trait_reference ->
  unmet:(Types.ty -> (string * Types.ty) option -> unit) ->
  unit

val fresh_arguments : State.state -> Path.t -> Types.argument list
val instantiate_type : State.state -> Source.Definition_span.t -> Path.t -> Types.argument list
val static_ : State.state -> Syntax.expression -> static_ option

val named_type :
  State.state -> Syntax.expression -> Path.t -> Syntax.bracket_item list option -> Types.ty

val type_argument_of_expression : State.state -> Syntax.expression -> Types.argument

val written_arguments :
  State.state -> Syntax.bracket_item list -> (Types.argument list, Types.ty) result

type instance = {
  signature : Types.signature;
  substitution : Types.substitution;
  type_arguments : Types.argument list;
}

val instantiate :
  State.state ->
  Source.Definition_span.t ->
  ?extra:(Types.parameter * Types.argument) list ->
  Types.signature ->
  instance

val function_signature : State.state -> Path.t -> Types.signature option
