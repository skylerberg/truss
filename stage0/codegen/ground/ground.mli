(* Ground types: fully monomorphic types, as code generation sees them after
   every type argument is substituted.

   The type checker's [Types.ty] also has generic parameters, projections,
   inference variables, literals, holes, and [Error]. None of them can reach
   code generation, so this type has no constructor for them, and a ground
   type is one that the type checker's substitution has fully decided.
   Definitions are named by [Path.t], as in every other stage. *)

type mode = Read | Mut | Own

type ty =
  | Named of { path : Path.t; arguments : argument list }
      (** Every built-in type but [Never] is [Named] after its path in [standard::intrinsic]. *)
  | Function of function_type
  | Any of { trait : Path.t; arguments : argument list; associated : (string * ty) list }
      (** [any Cursor[Element = Int64]], with every associated type fixed, sorted by name *)
  | Cursor of yielding  (** The nameless type of a pulled yielding method *)
  | Never

(* A [USize] generic argument is a value, as in [Array[UInt8, 32]], and a
   capability parameter's is the set of capabilities it stands for, sorted. *)
and argument = Type of ty | Value of Z.t | Capabilities of Path.t list

and function_type = { parameters : (mode * ty) list; result : result; uses : Path.t list }
(** [uses] is sorted, with every capability parameter replaced by the capabilities it stands for.
    Cost clauses do not change the code, so they are not here. *)

and result = Returns of ty | Yields of mode * ty | Lends of mode * ty

(* One yielding method, whose path names its receiver, with its generic
   arguments: the instance a cursor pulls from. *)
and yielding = { method_ : Path.t; type_arguments : argument list }

val compare : ty -> ty -> int
val compare_arguments : argument list -> argument list -> int
val equal : ty -> ty -> bool

(* The last part of a path, as a type is written: [List] for
   [standard::list::List]. *)
val path_name : Path.t -> string

(* A type as Truss writes it, such as [Option[List[Int64]]], for tests and
   messages. *)
val to_string : ty -> string
val argument_to_string : argument -> string

(* The canonical encoding, in deterministic CBOR, that instance keys and the
   LIR are hashed by. Each path is written by [path], which by default
   encodes it; test keys pass one that numbers paths, so that no name is in
   them. *)
val encode : ?path:(Path.t -> Cbor.t) -> ty -> Cbor.t
val encode_path : Path.t -> Cbor.t
val encode_argument : ?path:(Path.t -> Cbor.t) -> argument -> Cbor.t
val encode_mode : mode -> Cbor.t
