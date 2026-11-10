(** Types, and the interfaces of definitions.

    This library is shared by the type checker, the prover, and code generation, which depend on it
    without depending on the checker. *)

type mode = Read | Mut | Own  (** How a parameter or a receiver takes its value. *)

type parameter = { owner : Path.t; name : string }
(** A generic parameter, named by the definition that declares it and its name. Inside a trait,
    [Self] is the parameter named ["Self"] of the trait. *)

type literal_kind = Integer_literal | Float_literal

type ty =
  | Named of { path : Path.t; arguments : argument list }
      (** A type, trait, or capability definition with its arguments, and every built-in type but
          [Never] and [Integer]. *)
  | Parameter of parameter
  | Projection of { base : ty; trait : trait_reference; name : string }
      (** An associated type of a type that is not known yet: [Items.Element]. *)
  | Function of function_type
  | Any of trait_reference  (** [any Trait], with every associated type fixed. *)
  | Cursor of { method_ : Path.t; arguments : argument list }
      (** The nameless type of a pulled yielding method, with the method's type arguments. *)
  | Never
  | Integer  (** The mathematical integers, in specifications only. *)
  | Variable of int  (** An unknown type, while one statement is checked. *)
  | Literal of literal_kind * int  (** A literal whose type is not decided yet. *)
  | Hole  (** The type of a [todo] with nothing expected. *)
  | Error of Diagnostic.reported
      (** After an error, to stop cascades. Unifies with everything, which the proof that the error
          was reported makes safe. *)

and argument =
  | Type of ty
  | Value of value
  | Capabilities of capability list  (** What a [capability] parameter stands for, sorted. *)

and value =
  | Known of Z.t
  | Value_parameter of parameter
  | Value_variable of int  (** An unknown [USize] argument, while one statement is checked. *)

and trait_reference = {
  trait : Path.t;
  trait_arguments : argument list;
  associated : (string * ty) list;  (** Fixed associated types, sorted by name. *)
}

and function_type = {
  inputs : (mode * ty) list;
  output : result;
  uses : capability list;  (** Sorted. *)
  costs : cost list;
}

and result = Returns of ty | Yields of mode * ty | Lends of mode * ty

and capability =
  | Capability of Path.t
  | Capability_parameter of parameter
  | Capability_variable of int
      (** The set a call's capability parameter stands for, while a definition is checked: it is
          what the functions passed for the parameter use, which is known once the whole definition
          is. No result that is given out holds one. *)

and cost = { amortized : bool; resource : resource; bound : cost_bound }
(** A cost clause of a function type, which cannot mention parameters. Only the prover reads its
    bound; the checker reads whether there is a [time] clause. *)

(** What a function type's cost clause counts. Its [calls] counts the calls of a capability's
    methods, or of one of them: calls through a parameter are counted in a function's own clauses,
    which can name it. *)
and resource =
  | Time
  | Allocations
  | Allocated_bytes
  | Calls of { capability : Path.t; method_ : string option }

(** A function type's bound, which is a constant since its parameters have no names: the number,
    when it is written as one. *)
and cost_bound = Finite_cost | Order_of | No_more_than of Z.t option | Exactly_cost of Z.t option

val unit : ty
val bool : ty
val builtin : Intrinsic.builtin -> ty
val named : Path.t -> ty list -> ty
val is_builtin : Intrinsic.builtin -> ty -> bool
val builtin_of : ty -> Intrinsic.builtin option

val integer_types : Intrinsic.builtin list
(** The built-in integer types, which an integer literal can fill. *)

val float_types : Intrinsic.builtin list
val is_integer_type : ty -> bool
val is_signed : ty -> bool
val is_float_type : ty -> bool

(** {1 Substitution and equality} *)

type substitution = (parameter * argument) list

val substitute : substitution -> ty -> ty
val substitute_argument : substitution -> argument -> argument
val substitute_trait : substitution -> trait_reference -> trait_reference
val substitute_function : substitution -> function_type -> function_type

val map : (ty -> ty option) -> ty -> ty
(** Rewrites a type from the outside in: where [f] gives a replacement, it is used as it is, and
    elsewhere the type's parts are rewritten. Every part is visited: arguments, function inputs and
    outputs, [any] and projection traits. *)

val map_capabilities : (capability list -> capability list) -> ty -> ty
(** A type with every set of capabilities in it rewritten: the [uses] of each function type and each
    capability argument, at any depth. *)

val map_argument_capabilities : (capability list -> capability list) -> argument -> argument

val has_capability_variable : capability list -> bool
(** Whether a set has a {!Capability_variable} in it, so that what it holds is not known yet. *)

val equal : ty -> ty -> bool
(** Structural: types are nominal, so two [Named] types are equal when they name the same definition
    with equal arguments. *)

val is_error : ty -> bool

val contains_unsolved : ty -> bool
(** Whether a type still has a [Variable], [Literal], or [Hole] in it. *)

val terminates : function_type -> bool
(** Whether a function type has a [time] clause, which promises it terminates. *)

val same_clauses : function_type -> function_type -> bool
(** Whether two function types have the same [uses] and the same costs, in any order. *)

val costs_imply : given:cost list -> wanted:cost list -> bool
(** Whether costs promise what others ask, by their constants alone: each cost asked has one given
    for the same resource that is at least as strong, where an exact count is within any bound it
    does not exceed, a count is [O(...)], and every bound is [finite]. *)

(** {1 Showing types} *)

val show : ty -> string
(** As written in Truss: [List[Option[Int64]]], [fn(Int64) -> Bool]. *)

val show_trait : trait_reference -> string
val show_argument : argument -> string

(** {1 Interfaces}

    What other definitions may depend on: the checked outward-facing part of each definition. *)

type generic_kind =
  | Type_generic of trait_reference list  (** Bounds. *)
  | Value_generic  (** A [USize] value, as in [count: USize]. *)
  | Capability_generic

type generic = { generic : parameter; kind : generic_kind }

val capability_parameters : generic list -> parameter list

val substitution_of : generic list -> argument list -> substitution option
(** What stands for each of a definition's generic parameters, given its arguments in order, or
    [None] when there is not one argument for each parameter. *)

type parameter_info = { name : string; mode : mode; type_ : ty; has_default : bool }

type signature = {
  generics : generic list;  (** The type head's, then the function's own. *)
  receiver : (Path.receiver * ty) option;
      (** For a method: how it takes [self], and [self]'s type. *)
  parameters : parameter_info list;  (** Not counting [self]. *)
  output : result;
  uses : capability list;
  terminates : bool;  (** Whether it has a [time] clause. *)
  specification_only : bool;
      (** Whether it mentions [Integer], so it can be called only in specifications. *)
  stores_functions : string list;
      (** The [own] function-typed parameters, which accept only functions that capture nothing. *)
}

val map_signature : (ty -> ty) -> signature -> signature
(** A signature with each type of its receiver, parameters, and result rewritten. *)

val substitute_signature : substitution -> signature -> signature
(** A signature with a substitution made throughout: in its types, in the bounds of its generic
    parameters, and in its [uses]. *)

val method_in_impl :
  impl_generics:generic list -> impl_uses:capability list -> signature -> signature
(** The full signature of a method defined in an [impl]: the [impl]'s generic parameters come before
    the method's own, and the [impl]'s [uses] are added to the method's. *)

val function_type_of : signature -> function_type
(** A signature as the type of a function value, with [self] as its first input. *)

type field = { field_name : string; field_type : ty; field_has_default : bool }
type variant = { variant_name : string; fields : field list option; indirect : bool }

type shape =
  | Record of field list
  | Sum of variant list
  | Todo_type  (** [= todo]: it can be named and passed, but not used. *)
  | Builtin_type of Intrinsic.builtin
  | Error_shape of Diagnostic.reported  (** A type whose definition did not parse. *)

type type_interface = {
  type_generics : generic list;
  shape : shape;
  opaque : bool;  (** Whether its fields are hidden outside its package. *)
  derives : Path.t list;
}

type associated_type = { associated_name : string; associated_bounds : trait_reference list }

type trait_method = {
  method_name : string;
  method_receiver : Path.receiver;
  method_signature : signature;
  provided : bool;  (** Whether it has a body, so an [impl] need not write it. *)
}

type trait_interface = {
  trait_generics : generic list;  (** Not counting [Self]. *)
  requires : trait_reference list;
  associated_types : associated_type list;
  methods : trait_method list;
  is_capability : bool;
  broken_methods : (string * Diagnostic.reported) list;
      (** Members the parser could not read, whose uses get [Error]. *)
}

type impl_interface = {
  impl_generics : generic list;
  implements : trait_reference;  (** Its associated types are in [associated]. *)
  for_type : ty;
  impl_uses : capability list;
  impl_methods : (string * Path.receiver * signature) list;
  impl_broken : bool;  (** Whether the header did not parse, so it satisfies nothing it names. *)
}

type constant_interface = { constant_type : ty }
