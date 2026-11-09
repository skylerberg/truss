(** Types, and the interfaces of definitions. See TYPECHECKER.md, "Types" and "Checking signatures
    and definitions".

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
  | Error  (** After an error, to stop cascades. Unifies with everything. *)

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
and capability = Capability of Path.t | Capability_parameter of parameter

and cost = { amortized : bool; resource : string; bound : string }
(** A cost clause of a function type, which cannot mention parameters, spelled canonically. Only the
    prover reads its bound; the checker reads whether there is a [time] clause. *)

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

val equal : ty -> ty -> bool
(** Structural: types are nominal, so two [Named] types are equal when they name the same definition
    with equal arguments. *)

val contains_unsolved : ty -> bool
(** Whether a type still has a [Variable], [Literal], or [Hole] in it. *)

val terminates : function_type -> bool
(** Whether a function type has a [time] clause, which promises it terminates. *)

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

val function_type_of : signature -> function_type
(** A signature as the type of a function value, with [self] as its first input. *)

type field = { field_name : string; field_type : ty; field_has_default : bool }
type variant = { variant_name : string; fields : field list option; indirect : bool }

type shape =
  | Record of field list
  | Sum of variant list
  | Todo_type  (** [= todo]: it can be named and passed, but not used. *)
  | Builtin_type of Intrinsic.builtin
  | Error_shape  (** A type whose definition did not parse. *)

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
  broken_methods : string list;  (** Members the parser could not read, whose uses get [Error]. *)
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
