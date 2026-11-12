(** Name resolution.

    Resolution produces a definition's resolved form: tables, keyed by the tree's node ids, of the
    referent of every name and of the interpretation of each [name[...]]. The tree is unchanged. A
    definition reads other definitions only through the queries of {!Names}, so the database records
    every dependency. *)

module Names = Names
module Parts = Parts
module Prelude = Prelude

type specification_function = Walk.specification_function = Log | Power | Time | Calls

type target = Walk.target =
  | Binding  (** This name binds a local, a parameter, or a generic parameter. *)
  | Local of Syntax.id  (** A local or parameter, by the id of the name that binds it. *)
  | Law_parameter of int
      (** In a law's proof, a parameter of the law, by its position among the law's parameters. *)
  | Type_parameter of Types.parameter
      (** A generic type parameter, by the definition that declares it and its name. *)
  | Capability_parameter of Types.parameter  (** A generic parameter declared [capability Name]. *)
  | Value_parameter of Types.parameter  (** A [USize] generic parameter. *)
  | Definition of Names.named * Path.t  (** A definition, with its kind. *)
  | Variant of Path.t * string  (** A prelude variant written bare, such as [Some]. *)
  | Module of Path.module_
  | Field of string  (** A record's field, by name, in the record's invariant or potential. *)
  | Result_value  (** [result], in [ensures] and [cost]. *)
  | Old  (** [old], in specifications and proofs. *)
  | Identical  (** [identical], in specifications and proofs: identity, for every type. *)
  | Yielded
      (** [yielded]: the sequence of the parts that a lending or yielding method has yielded so far.
      *)
  | Finished  (** [finished], whether a yielding method ran to its end. *)
  | Specification_function of specification_function
  | Unknown of Diagnostic.reported  (** A name that refers to nothing, with its report. *)

type bracket = Walk.bracket =
  | Index
  | Type_arguments
  | Method_bracket  (** After a method's name, which type checking decides. *)

(** A value a name in scope means. *)
type value =
  | Value_local of Syntax.id  (** A local or parameter, by the id of the name that binds it. *)
  | Value_generic of Types.parameter  (** A [USize] generic parameter. *)
  | Value_field of string  (** A field, in a record's invariant or potential. *)
  | Value_law_parameter of int

type resolved = {
  names : target option array;
      (** By the id of each [Syntax.name]: the referent of the name, or [None] for a name that
          resolution leaves to type checking, such as a field, a label, or a variant in a pattern.
      *)
  brackets : bracket option array;  (** By the id of each [Bracket] expression. *)
  holes : (Syntax.id * (string * value) list) list;
      (** Each [todo], by its id, in the order of the walk, with the values in scope there, by name
          in order. *)
  diagnostics : Diagnostic.t list;  (** Relative to the definition. *)
}

type head = {
  name : Syntax.name;
  target : target;
  type_arguments : Syntax.bracket_item list option;
      (** The type arguments written after it, as in [parse[Int64]]. *)
}
(** The name that an expression denotes, if it is a name. *)

val head : resolved -> Syntax.expression -> head option
(** The name that an expression denotes: a name, inside any parentheses, with the type arguments
    written after it, so [parse], [(parse)], [parse[Int64]], and [(parse)[Int64]] all denote
    [parse]. [None] for an expression that is not a name, which computes a value. Every stage
    interprets a name with this function, so no two stages can disagree. *)

val resolved : (Names.key, resolved option) Query.query
(** A definition's resolved form, or [None] if there is no such definition. *)

val diagnostics : Query.context -> Path.module_ -> Diagnostic.t list
(** Every resolution error of a file, in its offsets and in order, including each definition's. *)

val closest : string -> string list -> string option
(** The candidate nearest to a name, if one is near enough to be a typo, for fixes that write the
    closest name. *)
