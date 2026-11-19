type ty =
  | Named of { path : Path.t; arguments : argument list }
  | Function of function_type
  | Any of { trait : Path.t; arguments : argument list; associated : (string * ty) list }
  | Never

and argument = Type of ty | Value of Z.t
and function_type = { parameters : (Language.Mode.t * ty) list; result : ty; uses : Path.t list }

type instantiation = {
  type_arguments : argument list;
  capability_arguments : (string * Path.t list) list;
}

val no_instantiation : instantiation
val compare : ty -> ty -> int
val make_builtin : ?arguments:argument list -> Language.Builtin_type.t -> ty
val to_string : ty -> string
val show_argument : argument -> string
