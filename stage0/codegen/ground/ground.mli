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
  | Never

(* A [USize] generic argument is a value, as in [Array[UInt8, 32]], and a
   capability parameter's is the set of capabilities it stands for, sorted. *)
and argument = Type of ty | Value of Z.t | Capabilities of Path.t list

and function_type = { parameters : (mode * ty) list; result : result; uses : Path.t list }
(** [uses] is the capabilities whose evidence a value of the type is called with. It is sorted, with
    every capability parameter replaced by the capabilities it is instantiated with, and without
    [Panic], which has no evidence. Cost clauses do not change the code, so they are not here. *)

and result = Returns of ty | Lends of mode * ty

val compare : ty -> ty -> int
val compare_arguments : argument list -> argument list -> int

(* The last part of a path, as a type is written: [List] for
   [standard::list::List]. *)
val path_name : Path.t -> string

(* A type as Truss writes it, such as [Option[List[Int64]]], for tests and
   messages. *)
val to_string : ty -> string
val argument_to_string : argument -> string
