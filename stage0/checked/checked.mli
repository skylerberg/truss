(** The published tables of a checked definition: the types, meanings, and calls that tools read by
    syntax node, such as hover, find references, and the unused-code check. The prover and code
    generation read the {!Core} form instead.

    The tables are dense arrays keyed by the tree's node ids, so they never copy the tree. Every
    type in them is solved: no [Variable] or [Literal] remains, and no unknown set of capabilities.
    A [Hole] stays where a [todo]'s type was never decided. A local is named by the id of the name
    that binds it. *)

type local = Syntax.id

(** How a trait's [impl] was found, for a call to a trait method. *)
type evidence =
  | Impl of { impl : Path.t; arguments : Types.substitution }  (** A written or derived [impl]. *)
  | Bound
      (** A bound in scope, on a generic parameter or on an associated type of one, resolved when
          the code is instantiated. *)
  | Dynamic  (** Through an [any] value's table. *)
  | Built_in  (** [Copyable] and [Plain], which the compiler implements. *)

type callee =
  | Function of { path : Path.t; type_arguments : Types.argument list }
      (** A named function or a type's own method, with its generic arguments, the type head's
          first. *)
  | Trait_method of {
      trait : Types.trait_reference;
      name : string;
      receiver : Path.receiver;
      self_type : Types.ty;
      type_arguments : Types.argument list;  (** The method's own generic arguments. *)
      evidence : evidence;
    }
  | Capability_method of { capability : Path.t; name : string }
  | Constructor of { type_ : Path.t; variant : string option; type_arguments : Types.argument list }
  | Function_value  (** A call through a function value, by position. *)
  | Intrinsic of { operation : Intrinsic.operation; type_arguments : Types.argument list }
  | Built_in_operator  (** [&&], [||], [!], and the bitwise operators, on built-in types. *)

(** The only conversions, each recorded where it happens. *)
type conversion =
  | From_never
  | Owned_to_view
      (** [List] to [Slice], or [String] to [StringSlice], passed to a parameter of the view type.
      *)
  | Function_widening  (** A function value to a function type with more [uses] or weaker costs. *)
  | To_integer  (** A built-in integer to [Integer], in specifications. *)
  | From_integer
      (** An [Integer] where a built-in integer is expected, which the prover shows fits. *)

type argument = {
  expression : Syntax.id;  (** The argument's expression. *)
  parameter : int;
      (** The parameter it goes to, counting a method's receiver as 0 and the rest after it. *)
  mode : Types.mode;
  conversion : conversion option;
}

type call = {
  callee : callee;
  arguments : argument list;  (** In the order written. *)
  defaults_left_out : string list;
      (** The parameters with defaults that were not passed, in order. *)
  uses : Types.capability list;
      (** The capabilities the call needs, with capability parameters substituted. *)
  result : Types.ty;
      (** What the callee gives. For an operator that tests what its call gives, as [<] tests the
          [Ordering] of [compare] and [!=] the [Bool] of [equal], it is not the operator's own type.
      *)
}

(** What a name or member expression means. *)
type meaning =
  | Local_value of local
  | Global of { path : Path.t; type_arguments : Types.argument list }
      (** A function as a value, or a constant. *)
  | Field_read of { type_ : Types.ty; field : string }
  | Variant_value of { type_ : Types.ty; variant : string }
      (** A variant with no fields, or one used as a function. *)
  | Type_name of Types.ty  (** A type before a [.], such as [Shape] in [Shape.Circle]. *)
  | Generic_value of Types.parameter  (** A [USize] generic parameter. *)
  | Specification_value  (** [result], [old], or a specification function. *)

type t = {
  types : Types.ty option array;  (** The type of every expression, by its id. *)
  local_types : Types.ty option array;  (** The type of every binding, by the id of its name. *)
  meanings : meaning option array;
      (** By the id of each [Name], [Member], or [Bracket] expression. *)
  calls : call option array;
      (** By the id of each call: a [Call], an operator, an index, and a compound assignment. *)
}

val show_meaning : meaning -> string
