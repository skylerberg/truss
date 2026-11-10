(** Name resolution.

    Resolution turns a definition's tree into its resolved form: tables, keyed by the tree's node
    ids, of what every name refers to and how each [name[...]] reads. The tree is unchanged. A
    definition reads other definitions only through the queries of {!Names}, so the database knows
    every one it read. *)

module Names = Names
module Parts = Parts
module Prelude = Prelude

type specification_function = Walk.specification_function = Log | Power | Time | Calls

type target = Walk.target =
  | Binding  (** This name binds a local, a parameter, or a generic parameter. *)
  | Local of Syntax.id  (** A local or parameter, by the id of the name that binds it. *)
  | Type_parameter of Types.parameter
      (** A generic type parameter, by the definition that declares it and its name. *)
  | Capability_parameter of Types.parameter  (** A generic parameter declared [capability Name]. *)
  | Value_parameter of Types.parameter  (** A [USize] generic parameter. *)
  | Definition of Names.named * Path.t  (** A definition, and what kind of definition it is. *)
  | Variant of Path.t * string  (** A prelude variant written bare, such as [Some]. *)
  | Module of Path.module_
  | Field of string  (** A record's field, by name, in the record's invariant or potential. *)
  | Result_value  (** [result], in [ensures] and [cost]. *)
  | Old  (** [old], in specifications and proofs. *)
  | Identical  (** [identical], in specifications and proofs: identity, for every type. *)
  | Yielded  (** [yielded], what a lending or yielding method handed out so far. *)
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

type resolved = {
  names : target option array;
      (** By the id of each [Syntax.name]: what the name refers to, or [None] for a name resolution
          leaves to type checking, such as a field, a label, or a variant in a pattern. *)
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
(** What an expression names, when it is a name. *)

val head : resolved -> Syntax.expression -> head option
(** What an expression names: a name, under any parentheses, with the type arguments written after
    it, so [parse], [(parse)], [parse[Int64]], and [(parse)[Int64]] all name [parse]. [None] for an
    expression that is not a name, which computes a value. Every stage reads a name this way, so
    none decides it differently. *)

val resolved : (Names.key, resolved option) Query.query
(** A definition's resolved form, or [None] if there is no such definition. *)

val file_diagnostics : (Path.module_, Diagnostic.t list) Query.query
(** The errors of a file's [use] lines, in the file's offsets: a module that does not exist, two
    imports with one last name, [standard::intrinsic] outside the standard library, and an import
    nothing uses, with a fix that deletes it. *)

val diagnostics : Query.context -> Path.module_ -> Diagnostic.t list
(** Every resolution error of a file, in its offsets and in order, including each definition's. *)

val closest : string -> string list -> string option
(** The candidate nearest to a name, if one is near enough to be a typo, for fixes that write the
    closest name. *)
