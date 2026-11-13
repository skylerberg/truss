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
  | Lent of lent
      (** The value of a constructor of lent places that a lending or yielding method yields. It
          owns nothing. *)
  | Never

(* A value of type [base] in which each of [fields] holds the address of a
   place of the field's type, or a lent value of its own. Every other field
   holds a value of a [Plain] type. The places are lent to be changed where
   [writable]. *)
and lent = { base : ty; writable : bool; fields : lent_field list }
and lent_field = { variant : string option; field : string; holds : holds }
and holds = Address | Nested of lent

(* A [USize] generic argument is a value, as in [Array[UInt8, 32]], and a
   capability parameter's is the set of capabilities it stands for, sorted. *)
and argument = Type of ty | Value of Z.t | Capabilities of Path.t list

and function_type = { parameters : (mode * ty) list; result : result; uses : Path.t list }
(** [uses] is the capabilities whose evidence a value of the type is called with. It is sorted, with
    every capability parameter replaced by the capabilities it is instantiated with, and without
    [Panic], which has no evidence. Cost clauses do not change the code, so they are not here. *)

and result = Returns of ty | Yields of mode * ty | Lends of mode * ty

(* One yielding method, whose path names its receiver, with its generic
   arguments: the instance a cursor pulls from. *)
and yielding = { method_ : Path.t; type_arguments : argument list }

val compare : ty -> ty -> int
val compare_arguments : argument list -> argument list -> int

(* The last part of a path, as a type is written: [List] for
   [standard::list::List]. *)
val path_name : Path.t -> string

(* A type as Truss writes it, such as [Option[List[Int64]]], for tests and
   messages. *)
val to_string : ty -> string
val argument_to_string : argument -> string
