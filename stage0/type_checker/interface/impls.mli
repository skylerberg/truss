(** Resolving the [impl] of a trait for a type, and normalizing associated types.

    By the orphan rule, an [impl] is defined in the package of its trait, of its type, or of the
    outermost type of one of the trait's arguments, so resolution searches only those packages. The
    [impl]s of each package are indexed once, by trait and type. Each lookup is a query over that
    index, so adding an [impl] re-checks only the definitions whose lookup result changed. *)

val head : Types.ty -> Path.t option
(** The outermost path of a type, which an [impl] is chosen by. *)

val derivable : Path.t -> bool

val index : (Path.package, ((Path.t * Path.t) * Path.t) list) Query.query
(** Every [impl] of a package, written or derived, by trait and type constructor. *)

val impls_for : Query.context -> Path.t -> Path.package -> (Path.t * Path.t) list
(** The impls of a package for a type, each with its trait. *)

val impls_in : (Path.t * Path.t * Path.package, Path.t list) Query.query
val cursor_trait : Path.t
val impl_interface : Query.context -> Path.t -> Types.impl_interface option

val trait_substitution : Query.context -> Path.t -> Types.substitution option
(** The substitution for an [impl] of a trait: the types that the trait's [Self] and parameters are
    instantiated with, in terms of the [impl]'s own generic parameters. It applies to a provided
    method that the [impl] inherits from the trait, and to the trait's clauses that a method of the
    [impl] inherits. *)

val match_type :
  variables:Types.parameter list ->
  Types.substitution ->
  Types.ty ->
  Types.ty ->
  Types.substitution option
(** Matches a type with an [impl]'s generic parameters in it against a type, extending the
    substitution, or fails. Inference variables and errors match anything, since a statement that
    has them is still being checked. *)

val match_arguments :
  variables:Types.parameter list ->
  Types.substitution ->
  Types.argument list ->
  Types.argument list ->
  Types.substitution option

type evidence =
  | From_impl of { impl : Path.t; substitution : Types.substitution }
  | From_bound
      (** A bound in scope, on a generic parameter or on an associated type of one, or a trait such
          a bound requires: the [impl] is found when the code is instantiated. *)
  | From_any  (** [any Trait] implements its trait. *)
  | Built_in  (** [Copyable] and [Plain], which the compiler implements. *)
  | Accepted of Types.ty
      (** This type satisfies every bound: it is an [Error], a [Hole], or a type that the statement
          has not inferred yet. A trait whose definition did not parse is satisfied by every type,
          with the [Error] of its report. *)

(** Whether a trait's method can be called through an [any] value, and if not, why. An [any] value
    has one compiled instance of each method, for the type that it hides. *)
type through_any =
  | Callable
  | Has_generics
      (** The method has generic parameters of its own, so it has an instance for each set of type
          arguments. *)
  | Names_self
      (** A parameter's type or the result's type names [Self], the hidden type, at any depth. An
          associated type of [Self] does not count: the [any] type fixes it. *)

val through_any : trait:Path.t -> Types.trait_method -> through_any
val copyable_path : Path.t

type bounds = Types.parameter -> Types.trait_reference list
(** The bounds in scope where a question is asked: each generic parameter's bounds, as the
    definition asking declares them. *)

val required : Types.generic list -> Types.substitution -> (Types.ty * Types.trait_reference) list
(** The obligations of a definition's bounds for given type arguments: each type argument, with a
    bound that it must satisfy. *)

val implements :
  Query.context ->
  bounds:bounds ->
  ?depth:int ->
  ?conditions:bool ->
  Types.ty ->
  Types.trait_reference ->
  evidence option
(** The evidence that a type implements a trait. Without [conditions], it is the [impl] whose head
    matches the type, whether or not the bounds on the [impl]'s parameters hold. An associated type
    is read from that [impl]: a bound that does not hold is reported where the trait is required,
    and normalizing the associated type reads nothing more about the type's arguments. *)

val associated_type :
  Query.context ->
  bounds:bounds ->
  ?defining:Path.t list ref ->
  Types.ty ->
  Types.trait_reference ->
  string ->
  Types.ty option
(** The associated type a trait's [impl] for a type chooses, or [None]. [defining] collects the
    [impl] that defines it. *)

val capability_set :
  Query.context ->
  bounds:bounds ->
  ?depth:int ->
  Types.ty ->
  Types.trait_reference ->
  string ->
  Types.capability_set
(** The associated capability set of a type, as the trait's [impl] for the type defines it. The set
    of a generic parameter is known only for each instantiation, so it stays a projection, and so
    does the set of a type that is not inferred yet. An [any] type fixes every set to the empty one:
    the code that holds the value cannot name the capabilities of the type that it hides. *)

val normalize_capabilities :
  Query.context -> bounds:bounds -> ?depth:int -> Types.capability_set -> Types.capability_set
(** Normalizes a set of capabilities: replaces every associated capability set whose type is known
    by the capabilities that the [impl] defines for it. *)

val normalize : Query.context -> bounds:bounds -> ?defining:Path.t list ref -> Types.ty -> Types.ty
(** Normalizes a type: replaces every projection whose base is known by the [impl]'s definition of
    the associated type, and normalizes every set of capabilities in the type. A projection on a
    generic parameter stays, unless a bound fixes it. So does a projection that no [impl] defines,
    which then equals only itself. [defining] collects the [impl]s whose definitions replace
    associated types. *)

val signature : Query.context -> Path.t -> Types.signature option
(** The signature of the function or method at a path, for every path at which code is compiled or
    proven. A method that an [impl] inherits from its trait, or a method of a derived [impl], is not
    written in the [impl]: its signature is the trait method's, with [Self] and the trait's
    parameters substituted by the [impl]'s types, inside that [impl]. Its [uses] are the trait
    method's for the [impl]'s type, so [Self.Uses] is the set that the [impl] defines. *)

val copyable : Query.context -> bounds:bounds -> Types.ty -> bool
val plain : Query.context -> bounds:bounds -> Types.ty -> bool
val is_view : Query.context -> bounds:bounds -> Types.ty -> bool
val holds_function : Query.context -> bounds:bounds -> Types.ty -> bool
val contents : Query.context -> bounds:bounds -> Types.ty -> Properties.contents
