(** Instantiating definitions while a statement is checked: fresh arguments for a generic
    definition, its bounds as deferred requirements, and type arguments written in expressions. *)

open State
module T = Types

type static_ =
  | Static_type of T.ty
  | Static_trait of Path.t * T.argument list option
  | Static_capability of Path.t

val require :
  state ->
  at:Syntax.span ->
  Unify.T.ty ->
  T.trait_reference ->
  unmet:(Types.ty -> (string * Types.ty) option -> unit) ->
  unit

val fresh_arguments : state -> Path.t -> T.argument list
val instantiate_type : state -> Syntax.span -> Path.t -> T.argument list
val static_ : state -> Syntax.expression -> static_ option
val named_type : state -> Syntax.expression -> Path.t -> Syntax.bracket_item list option -> T.ty
val type_argument_of_expression : state -> Syntax.expression -> T.argument

type instance = {
  signature : T.signature;
  substitution : T.substitution;
  type_arguments : T.argument list;
}

val instantiate :
  state -> Syntax.span -> ?extra:(T.parameter * T.argument) list -> T.signature -> instance

val function_signature : state -> Path.t -> (Types.signature, Diagnostic.reported) result option
