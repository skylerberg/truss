type mode = Read | Mut | Own

type ty =
  | Named of { path : Path.t; arguments : argument list }
  | Function of function_type
  | Any of { trait : Path.t; arguments : argument list; associated : (string * ty) list }
  | Never

and argument = Type of ty | Value of Z.t | Capabilities of Path.t list
and function_type = { parameters : (mode * ty) list; result : result; uses : Path.t list }
and result = Returns of ty | Lends of mode * ty

val compare : ty -> ty -> int
val path_name : Path.t -> string
val to_string : ty -> string
val argument_to_string : argument -> string
