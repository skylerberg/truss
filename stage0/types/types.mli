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
  | Capabilities of capability_set  (** What a [capability] parameter stands for. *)

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
  uses : capability_set;
  costs : cost list;
}

and result = Returns of ty | Yields of mode * ty | Lends of mode * ty

and capability =
  | Capability of Path.t
  | Capability_parameter of parameter
  | Capability_projection of { base : ty; trait : trait_reference; name : string }
      (** An associated capability set of a type that is not known yet: [Source.Uses]. Its trait
          reference fixes no associated type, so that two projections of one set are equal. *)
  | Capability_variable of int
      (** The set a call's capability parameter stands for, while a definition is checked: it is the
          union of the capabilities the arguments for the parameter use, which is known once the
          whole definition is checked. No result that is given out holds one. *)

and capability_set = private capability list
(** A set of capabilities, kept sorted and without duplicates so that equal sets are equal values.
    Only {!capability_set} builds one. *)

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

val is_well_known : Well_known.t -> ty -> bool
(** Whether a type is the well-known type or an instantiation of it: [is_well_known List] holds for
    [List[Int64]]. *)

val integer_bits : ?usize_bits:int -> ty -> (int * bool) option
(** The bits of a built-in integer type and whether it is signed. [USize] and [ISize] have
    [usize_bits], 64 when it is not given. *)

val integer_range : ?usize_bits:int -> ty -> (Z.t * Z.t) option
(** The least and the greatest value of a built-in integer type, with [USize] and [ISize] as
    {!integer_bits} has them. *)

val is_integer_type : ty -> bool
val is_signed : ty -> bool
val is_float_type : ty -> bool

(** {1 Capability sets} *)

val capability_set : capability list -> capability_set
val no_capabilities : capability_set
val capability_union : capability_set -> capability_set -> capability_set
val capability_subset : capability_set -> capability_set -> bool

val capability_difference : capability_set -> capability_set -> capability_set
(** The capabilities of the first set that the second does not hold. *)

val flat_map_capabilities : (capability -> capability list) -> capability_set -> capability_set
(** The set of everything [f] gives for each capability of a set. *)

(** {1 Substitution and equality} *)

type substitution = (parameter * argument) list

val substitute : substitution -> ty -> ty
val substitute_argument : substitution -> argument -> argument
val substitute_trait : substitution -> trait_reference -> trait_reference
val substitute_function : substitution -> function_type -> function_type
val substitute_capabilities : substitution -> capability_set -> capability_set

val result_type : result -> ty
(** The type of what a function returns, yields, or lends. *)

val show_mode : mode -> string
(** How a mode is written before a type: [""], ["mut "], or ["own "]. *)

val map : ?capabilities:(capability_set -> capability_set) -> (ty -> ty option) -> ty -> ty
(** Rewrites a type from the outside in: where [f] gives a replacement, it is used as it is, and
    elsewhere the type's parts are rewritten. Every part is visited: arguments, function inputs and
    outputs, [any] and projection traits. [capabilities] rewrites each set of capabilities among
    those parts: the [uses] of a function type, and a capability argument. *)

val exists : ?resolve:(ty -> ty) -> (ty -> bool) -> ty -> bool
(** Whether [f] holds for a type or any of its parts, the parts {!map} visits. [resolve] is applied
    to each type before it is tested and taken apart, for a type with variables bound elsewhere. *)

val has_capability_variable : capability_set -> bool

val capabilities_unsolved : capability_set -> bool
(** Whether what a set holds is not known yet: it has a {!Capability_variable}, or an associated
    capability set of a type that is not inferred yet. *)

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

val costs_imply : provided:cost list -> required:cost list -> bool
(** Whether costs promise what others ask, by their constants alone: each cost asked has one given
    for the same resource that is at least as strong, where an exact count is within any bound it
    does not exceed, a count is [O(...)], and every bound is [finite]. *)

(** {1 Showing types} *)

val show : ty -> string
(** As written in Truss: [List[Option[Int64]]], [fn(Int64) -> Bool]. *)

val show_capability : capability -> string
val show_trait : trait_reference -> string
val show_argument : argument -> string

val show_output : result -> string
(** A function's result as a signature writes it after the parameters: [" -> Int64"],
    [" yields mut Element"], or nothing for unit. *)

(** {1 Interfaces}

    What other definitions may depend on: the checked outward-facing part of each definition. *)

type generic_kind =
  | Type_generic of trait_reference list  (** Bounds. *)
  | Value_generic  (** A [USize] value, as in [count: USize]. *)
  | Capability_generic

type generic = { generic : parameter; kind : generic_kind }

val generic_arguments : generic list -> argument list
(** The arguments that name each generic itself, as the definition's own body sees them. *)

val bounds_of : generic list -> parameter -> trait_reference list
(** The bounds a list of generics gives one type parameter. *)

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
  uses : capability_set;
  terminates : bool;  (** Whether it has a [time] clause. *)
  specification_only : bool;
      (** Whether it mentions [Integer], so it can be called only in specifications. *)
  stores_functions : string list;
      (** The [own] function-typed parameters, which accept only functions that capture nothing. *)
  transparent : bool;
      (** Whether the proofs of callers in other packages can read the body
          ([public transparent fn]). *)
}

val body_is_definition : signature -> bool
(** Whether a function with this signature is one in the logic, whose body defines it: it
    terminates, uses no capability, mutates no argument, and returns its result. *)

val map_signature : (ty -> ty) -> signature -> signature
(** A signature with each type of its receiver, parameters, and result rewritten. *)

val substitute_signature : substitution -> signature -> signature
(** A signature with a substitution made throughout: in its types, in the bounds of its generic
    parameters, and in its [uses]. *)

val method_in_impl :
  impl_generics:generic list -> impl_uses:capability_set -> signature -> signature
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
  associated_capabilities : string list;
      (** The associated capability sets the trait declares, as in [capability Uses]. *)
  methods : trait_method list;
  laws : (string * (string * ty) list) list;
      (** Each law's name, and its parameters' names and types. A proof of the law names them. *)
  is_capability : bool;
  broken_methods : (string * Diagnostic.reported) list;
      (** Members the parser could not read, whose uses get [Error]. *)
}

type impl_interface = {
  impl_generics : generic list;
  implements : trait_reference;  (** Its associated types are in [associated]. *)
  for_type : ty;
  impl_uses : capability_set;
  capability_sets : (string * capability_set) list;
      (** The associated capability sets the [impl] defines, sorted by name. A set that the trait
          declares and the [impl] leaves out is empty. *)
  impl_methods : (string * Path.receiver * signature) list;
  impl_broken : bool;  (** Whether the header did not parse, so it satisfies nothing it names. *)
}

type constant_interface = { constant_type : ty }
