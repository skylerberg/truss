(** The type checker's queries. *)

(** Looking up a member, the name after a dot. *)
module Members : sig
  val trait_methods : Query.context -> Path.t -> string -> Types.trait_method list
  (** The versions of a trait method: one for each receiver mode. *)

  val trait_method : Query.context -> Path.t -> string -> Path.receiver -> Types.trait_method option

  val fields : Query.context -> Path.t -> Types.argument list -> Types.field list option
  (** The fields of a record type, with its type arguments substituted. *)

  val variants : Query.context -> Path.t -> Types.argument list -> Types.variant list option
  (** The variants of a sum type, with its type arguments substituted. *)

  val shape : Query.context -> Path.t -> Types.shape option
end

type result = Body.result = {
  checked : Checked.t;
  core : Core.t option;
      (** The definition's core form, when it parsed whole and nothing in it is an error. *)
  diagnostics : Diagnostic.t list;
  evidence : Path.package list;  (** The packages whose [impl]s met a bound in the definition *)
}

val checked : (Resolve.Names.key, result option) Query.query

val diagnostics : Query.context -> Path.module_ -> Diagnostic.t list
(** The diagnostics of every body in a file, in file offsets and in order. *)

val derived : (Path.t, Core.t option) Query.query
(** The core form of a method of a derived [impl], by the method's path. It is generated once,
    however many instances of the method are compiled. *)

val core : (Resolve.Names.key, Core.t option) Query.query
(** The core form of a definition. [None] if the definition has an error. *)

val core_of_path : (Path.t, (Core.t * Types.substitution) option) Query.query
(** The core form of the function or method at a path, with a substitution to apply to it.

    - A function or method with a written body: its own core form, and the empty substitution.
    - A method of a derived [impl]: the generated core form, and the empty substitution.
    - A method that an [impl] inherits from its trait: the core form of the trait's default method,
      and the substitution that maps [Self] and the trait's generic parameters to the [impl]'s
      types. *)

val specification : (Resolve.Names.key, Core.t option) Query.query
(** What a caller's proof reads of a definition: its core form, without the body of a function whose
    body no caller's proof reads. The parameters and the contract are built before the body, so
    their nodes are numbered the same whatever the body is. Editing such a body leaves this result
    equal, and no caller is proven again.

    In the function's own package, a caller's proof reads the body of a function in the logic, which
    the body defines. In another package, it reads that body only if the function is [transparent]:
    a body that other packages' proofs read is part of the package's interface, and only a marked
    one is. In every package, it reads the body that a trait provides for a method, which an [impl]
    inherits or must agree with. It never reads the body of a theorem: a call of a theorem asserts
    the [requires] and assumes the [ensures]. *)

val exported_specification : (Resolve.Names.key, Core.t option) Query.query
(** What a caller's proof in another package reads of a definition. Editing the body of a function
    that is not [transparent] leaves this result equal, so no proof in a package that depends on
    this one runs again. *)

val specification_of_path : (Path.t, (Core.t * Types.substitution) option) Query.query
(** As {!core_of_path}, for {!specification}. *)

val exported_specification_of_path : (Path.t, (Core.t * Types.substitution) option) Query.query
(** As {!core_of_path}, for {!exported_specification}. *)

val evidence : (Resolve.Names.key, Path.package list) Query.query
(** The packages whose [impl]s met a bound in a definition. *)

val clean : Query.context -> Resolve.Names.key -> Checked.t option
(** The checked tables of a definition, or [None] if the definition has a parse error, a resolution
    error, or a type error. The pattern, use, and ownership checks run only on a definition that has
    none, so that one mistake is not reported again by a later check. *)

val is_clean : Query.context -> Resolve.Names.key -> bool
