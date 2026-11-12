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

(** What a name, member, or bracket expression resolves to, once types are known. *)
type resolution = Tables.resolution =
  | Local_value of Syntax.id  (** A local, by the id of the name that binds it. *)
  | Global of { path : Path.t; type_arguments : Types.argument list }
      (** A function as a value, or a constant. *)
  | Field_access of { type_ : Types.ty; field : string }
  | Variant_value of { type_ : Types.ty; variant : string }
      (** A variant with no fields, or one used as a function. *)
  | Type_name of Types.ty  (** A type before a [.], such as [Shape] in [Shape.Circle]. *)
  | Value_parameter of Types.parameter  (** A [USize] generic parameter. *)
  | Specification_value  (** [result], [old], or a specification function. *)

val show_resolution : resolution -> string

type tables = Tables.published = {
  types : Types.ty option array;  (** The type of every expression, by its id. *)
  local_types : Types.ty option array;  (** The type of every binding, by the id of its name. *)
  resolutions : resolution option array;
      (** By the id of each [Name], [Member], or [Bracket] expression. *)
  callees : Path.t option array;
      (** By the id of each call of a named function or a type's own method: the callee's path. *)
}
(** What tools read of a checked definition, such as hover, find references, and the unused-code
    check. The prover and code generation read the core form instead. Each table is a dense array
    keyed by the syntax tree's node ids. Every type in them is solved: no [Variable] or [Literal]
    remains, and no unknown set of capabilities. A [Hole] stays where a [todo]'s type was never
    decided. *)

type type_check_result = Body.type_check_result = {
  tables : tables;
  core : Core.t option;
      (** The definition's core form, when it parsed whole and nothing in it is an error. *)
  diagnostics : Syntax.diagnostic list;
  evidence : Path.package list;  (** The packages whose [impl]s met a bound in the definition *)
}

val type_check_result : (Resolve.Names.key, type_check_result option) Query.query

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

    A caller's proof never reads the body of a function or of a method of a type: it reads the
    contract. In every package, it reads the body that a trait provides for a method, which an
    [impl] inherits or must agree with, and in the [impl]'s own package the body of an [impl]'s
    method, whose contract is the trait's. It never reads the body of a theorem: a call of a theorem
    asserts the [requires] and assumes the [ensures]. *)

val exported_specification : (Resolve.Names.key, Core.t option) Query.query
(** What a caller's proof in another package reads of a definition. Editing the body of a function
    leaves this result equal, so no proof in a package that depends on this one runs again. *)

val specification_of_path : (Path.t, (Core.t * Types.substitution) option) Query.query
(** As {!core_of_path}, for {!specification}. *)

val exported_specification_of_path : (Path.t, (Core.t * Types.substitution) option) Query.query
(** As {!core_of_path}, for {!exported_specification}. *)

val evidence_packages : (Resolve.Names.key, Path.package list) Query.query
(** The packages whose [impl]s met a bound in a definition. *)

val clean_tables : Query.context -> Resolve.Names.key -> tables option
(** The tables of a definition, or [None] if the definition has a parse error, a resolution error,
    or a type error. The pattern, use, and ownership checks run only on a definition that has none,
    so that one mistake is not reported again by a later check. *)

val is_clean : Query.context -> Resolve.Names.key -> bool
