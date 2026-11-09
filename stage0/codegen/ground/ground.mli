(* Ground types: fully monomorphic types, as code generation sees them after
   every type argument is substituted. See CODEGEN.md, "Instances".

   The type checker's [Types.ty] also has generic parameters, projections,
   inference variables, literals, holes, and [Error]. None of them can reach
   code generation, so this type has no constructor for them, and a ground
   type is one that the type checker's substitution has fully decided. *)

(* A definition, named by its package, module path, and name, never by hash,
   as DESIGN.md's hash format requires. A method or a constant under a type
   is named by its type's definition and its own name. *)
type definition = { package : string; modules : string list; name : string }
type mode = Read | Mut | Own

type ty =
  | Named of { definition : definition; arguments : argument list }
      (** Every built-in type is [Named] after the prelude definition the compiler provides, such as
          [Int64] or [Array]. *)
  | Function of function_type
  | Any of { trait : definition; arguments : argument list; associated : (string * ty) list }
      (** [any Cursor[Element = Int64]], with every associated type fixed, sorted by name *)
  | Cursor of yielding  (** The nameless type of a pulled yielding method *)
  | Never

(* A [USize] generic argument is a value, as in [Array[UInt8, 32]]. *)
and argument = Type of ty | Value of Z.t

and function_type = { parameters : (mode * ty) list; result : result; uses : definition list }
(** [uses] is sorted by [compare_definition], with every capability parameter already replaced by
    the capabilities it stands for. Cost clauses do not change the code, so they are not here. *)

and result = Returns of ty | Yields of mode * ty | Lends of mode * ty

(* One yielding method with its receiver mode and arguments: the instance a
   cursor pulls from. *)
and yielding = {
  method_ : definition;
  receiver : mode;
  type_arguments : argument list;
  capabilities : definition list list;
}

val compare_definition : definition -> definition -> int
val compare : ty -> ty -> int
val compare_arguments : argument list -> argument list -> int
val equal : ty -> ty -> bool

(* [standard::list::List], as Truss writes it. *)
val definition_to_string : definition -> string

(* A type as Truss writes it, such as [Option[List[Int64]]], for tests and
   messages. *)
val to_string : ty -> string

(* The canonical encoding, in deterministic CBOR, that instance keys and the
   LIR are hashed by. *)
val encode : ty -> Cbor.t
val encode_definition : definition -> Cbor.t
val encode_argument : argument -> Cbor.t
val encode_mode : mode -> Cbor.t
