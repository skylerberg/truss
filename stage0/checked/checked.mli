(** The checked form of a definition: what the prover and code generation read.

    It is a set of dense tables keyed by the tree's node ids, so it never copies the tree. Every
    type in it is solved: no [Variable] or [Literal] remains, and no unknown set of capabilities. A
    [Hole] stays where a [todo]'s type was never decided. A local is named by the id of the name
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
  | Specification_value  (** [result], [old], or a cost function. *)

type literal =
  | Integer_value of Z.t
  | Float_value of float
      (** Already rounded to the literal's type; a [Float32] is rounded to 32 bits. *)

(** What a [for] loop drives. *)
type loop =
  | Integer_range of { element : Types.ty; inclusive : bool }
      (** A counted loop over built-in integers. *)
  | Yielding of { call : call; mode : Types.mode }
      (** A call to a [yields] method, [each] or written out. *)
  | Pulled of { cursor : Types.ty }  (** A cursor, pulled until it ends. *)

type pattern =
  | Variant_pattern of { type_ : Types.ty; variant : string }
  | Record_pattern of { type_ : Types.ty }
  | Constant_pattern of Path.t
  | Literal_pattern of literal
  | Other_pattern

type template = {
  from_template : call option;  (** The tag's [from_template]; [None] for a plain string. *)
  part_conversions : call option list;
      (** For each interpolated value: its [From] conversion to the tag's [Part], or for a plain
          string, its [Display]. *)
  interpolated : bool;
}

(** An obligation the type checker creates, which the prover discharges. *)
type obligation =
  | Disjoint of { first : Syntax.id; second : Syntax.id }
  | Integer_fits of { expression : Syntax.id; type_ : Types.ty }
  | Costs_imply of {
      expression : Syntax.id;
      given : Types.function_type;
      expected : Types.function_type;
    }
  | Guards_cover of { match_ : Syntax.id }

type provided = { capability : Path.t; impl : Path.t; arguments : Types.substitution }
(** One capability an implementation provides: the [impl] that provides it, with the [impl]'s
    generic arguments. *)

type provide = { implementations : (Syntax.id * provided list) list }
(** What a [provide] builds: for each implementation, by its expression's id, the capabilities its
    type provides. *)

type t = {
  types : Types.ty option array;  (** The type of every expression, by its id. *)
  local_types : Types.ty option array;  (** The type of every binding, by the id of its name. *)
  meanings : meaning option array;
      (** By the id of each [Name], [Member], or [Bracket] expression. *)
  calls : call option array;
      (** By the id of each call: a [Call], an operator, an index, and a compound assignment. *)
  literals : literal option array;
      (** By the id of each literal expression, literal pattern, and literal end of a range pattern.
      *)
  patterns : pattern option array;  (** By the id of each pattern. *)
  pattern_types : Types.ty option array;
      (** The type of the value each pattern matches, by its id. *)
  loops : loop option array;  (** By the id of each [for] statement. *)
  templates : template option array;  (** By the id of each string literal. *)
  captures : local list option array;
      (** By the id of each lambda: the outer locals it reads, in order, with [self] named by the
          definition's own id. *)
  own_operator : bool array;
      (** By the id of each compound assignment: whether [own self]'s version was chosen. *)
  provides : provide option array;  (** By the id of each [provide]. *)
  lends : Types.mode option array;
      (** By the id of each call of a lending method: how the part it gives is lent, read-only or
          [mut]. The part lasts the rest of the caller's statement. *)
  obligations : obligation list;
}

val create : int -> t
(** Empty tables for a definition with that many nodes. *)

val type_of : t -> Syntax.expression -> Types.ty
(** The type of an expression of a body that checked, where every expression has one. One without is
    a bug in the compiler, raised as one: the stages after checking run on what it decided, and
    never guess where it decided nothing. *)

val pattern_type : t -> Syntax.pattern -> Types.ty
(** The type of the value a pattern matches, as {!type_of}. *)

val show_meaning : meaning -> string
