(** Name resolution.

    Resolution turns a definition's tree into its resolved form: tables, keyed by the tree's node
    ids, of what every name refers to and how each [name[...]] reads. The tree is unchanged. A
    definition reads other definitions only through the queries of {!Names}, so the database knows
    every one it read. *)

module Names = Names
module Parts = Parts
module Prelude = Prelude

type cost_function = Walk.cost_function = Log | Power | Time | Calls

type target = Walk.target =
  | Binding  (** This name binds a local, a parameter, or a generic parameter. *)
  | Local of Syntax.id  (** A local or parameter, by the id of the name that binds it. *)
  | Generic of Syntax.id  (** A generic parameter of the definition, by the id of its name. *)
  | Definition of Path.t
  | Variant of Path.t * string  (** A prelude variant written bare, such as [Some]. *)
  | Module of Path.module_
  | Field of string  (** A record's field, by name, in the record's invariant or potential. *)
  | Result_value  (** [result], in [ensures] and [cost]. *)
  | Old  (** [old], in specifications and proofs. *)
  | Cost_function of cost_function
  | Unknown  (** A name that refers to nothing; its error is reported. *)

type bracket = Walk.bracket =
  | Index
  | Type_arguments
  | Method_bracket  (** After a method's name, which type checking decides. *)

(** A value a name in scope means. *)
type value =
  | Value_local of Syntax.id  (** A local or parameter, by the id of the name that binds it. *)
  | Value_generic of Syntax.id  (** A [USize] generic parameter, by the id of its name. *)
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
