type key =
  | Code of { path : Path.t; type_arguments : Ground.argument list }
  | Constant of Path.t
  | Drop of Ground.ty
  | Copy of Ground.ty
  | Debug of Ground.ty
  | Any_drop of Ground.ty
  | Encode of Ground.ty
  | Evaluator of Path.t
  | Template_check of { from_template : Path.t; literals : string list; clauses : int list }
  | Call_evaluation of { function_ : Path.t; arguments : Z.t list }
  | Adapter of { function_ : key; ty : Ground.function_type }
  | Entry of key
  | Table of { impl : Path.t; type_arguments : Ground.argument list }
  | Program_main of Path.t
  | Any_entry of key
  | Any_table of { impl : Path.t; type_arguments : Ground.argument list }
  | Locked_entry of { capability : Path.t; name : string }
  | Locked_table of Path.t

val compare : key -> key -> int
val equal : key -> key -> bool
val symbol : key -> string
val path_symbol : Path.t -> string
val type_symbol : Ground.ty -> string
val to_string : key -> string
