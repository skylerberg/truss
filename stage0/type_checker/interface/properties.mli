(** The properties of a type that are derived from its shape: [Copyable], [Plain], the view
    property, and the types that it contains.

    An opaque type is [Copyable] or [Plain] only when it declares so with [derives]. It then has the
    property under the conditions that its fields give, as any other type does: [Slice[Element]] is
    [Plain] for every [Element], because it holds a view of its elements, and [List[Element]] is
    [Copyable] when [Element] is. A generic parameter has these properties only when it is bounded
    by them, and an associated type of a parameter only when its declared bounds include them. The
    view property is part of a type's shape, so it is derived from the fields. *)

val copyable_trait : Path.t
val plain_trait : Path.t
val storable_trait : Path.t

val trait_substitution :
  Types.trait_interface -> self:Types.ty -> Types.trait_reference -> Types.substitution
(** The substitution for a trait reference: the types that the trait's [Self] and parameters are
    instantiated with. A reference with the wrong number of arguments, which lowering reported,
    substitutes [Self] only: an unsubstituted parameter equals no type. *)

val bound_closure :
  Query.context ->
  ?seen:Types.trait_reference list ->
  self:Types.ty ->
  Types.trait_reference ->
  Types.trait_reference list
(** The closure of a bound on a type: the bound's trait and, transitively, the traits that it
    requires, with [Self] in the required traits substituted by the type. *)

val known_bounds :
  Query.context ->
  bounds:(Types.parameter -> Types.trait_reference list) ->
  Types.ty ->
  Types.trait_reference list
(** The traits that a type implements according to bounds: the bounds of a generic parameter, or the
    declared bounds of a projection, each with its closure. *)

type property =
  | Copyable
  | Plain
  | View
  | Holds_function
      (** A value of the type can hold a function value: the type is a function type, or a type
          whose value is of an unknown type, or it has a part that is one. *)

(** How a type occurs in a value of another type. *)
type occurrence =
  | In_place  (** In a field of a variant that is not [indirect], or in an array. *)
  | Indirect
      (** Behind a pointer: in an [indirect] variant, a collection's storage, an [any], or the
          output of a function type. *)
  | Function_input  (** At any depth in the input of a function type that has a [time] clause. *)

val through : occurrence -> occurrence -> occurrence
(** The occurrence of a type in a value that contains it through another type. *)

type recursion = {
  recursive : Types.ty;
  occurrence : occurrence;  (** How the type occurs in itself. *)
  defining : Path.t list;
      (** The [impl]s whose definitions of associated types the type contains itself through. *)
}
(** A named type that contains itself through its arguments. No type definition's fields name such a
    type: [Kept[Marker]] is one when [Kept[Source]] has a field of type [Source.Part] and [Marker]'s
    [impl] defines [Part] as [Kept[Marker]]. *)

type contents = {
  contained : (Types.ty * occurrence) list;
      (** Named types, parameters, and associated types, including those in the arguments of generic
          types. *)
  recursions : recursion list;
}
(** The types that a value of a type contains. *)

val has :
  Query.context ->
  bounds:(Types.parameter -> Types.trait_reference list) ->
  normalize:(Types.ty -> Types.ty) ->
  property ->
  Types.ty ->
  bool
(** Whether a type has a property. [bounds] gives the bounds of each generic parameter in scope, and
    [normalize] replaces an associated type by its definition in the matching [impl]. An associated
    type that no [impl] defines is assumed not to be [Copyable] or [Plain], and to be a view. *)

val storable :
  Query.context ->
  bounds:(Types.parameter -> Types.trait_reference list) ->
  normalize:(Types.ty -> Types.ty) ->
  Types.ty ->
  bool
(** Whether a type is [Storable]: it is not a view type for every instantiation of its generic
    parameters. A generic parameter, or an associated type of one, is [Storable] only when it is
    bounded by [Storable], because it may be instantiated with a view type. So [List[Element]] is
    [Storable] where [Element] is. *)

val contents :
  Query.context -> normalize:(Types.ty -> Types.ty * Path.t list) -> Types.ty -> contents
(** The types that a value of a type contains. [normalize] normalizes a type and gives the [impl]s
    whose definitions replaced its associated types. *)
