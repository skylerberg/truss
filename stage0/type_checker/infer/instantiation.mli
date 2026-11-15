open State

type static_ =
  | Static_type of Types.ty
  | Static_trait of Path.t * Types.argument list option
  | Static_capability of Path.t

val require :
  state ->
  at:Source.Definition_span.t ->
  Types.ty ->
  Types.trait_reference ->
  unmet:(Types.ty -> (string * Types.ty) option -> unit) ->
  unit

val fresh_arguments : state -> Path.t -> Types.argument list
val instantiate_type : state -> Source.Definition_span.t -> Path.t -> Types.argument list
val static_ : state -> Syntax.expression -> static_ option
val named_type : state -> Syntax.expression -> Path.t -> Syntax.bracket_item list option -> Types.ty
val type_argument_of_expression : state -> Syntax.expression -> Types.argument

type instance = {
  signature : Types.signature;
  substitution : Types.substitution;
  type_arguments : Types.argument list;
}

val instantiate :
  state ->
  Source.Definition_span.t ->
  ?extra:(Types.parameter * Types.argument) list ->
  Types.signature ->
  instance

val function_signature : state -> Path.t -> Types.signature option
