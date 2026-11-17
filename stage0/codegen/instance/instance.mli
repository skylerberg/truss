type key =
  | Code of { path : Path.t; type_arguments : Ground.argument list }
  | Constant of Path.t
  | Drop of Ground.ty
  | Copy of Ground.ty
  | Debug of Ground.ty
  | Any_drop of Ground.ty
  | Any_copy of Ground.ty
  | Encode of Ground.ty
  | Evaluator of Path.t
  | Literal_check of literal_check
  | Call_evaluation of { function_ : Path.t; arguments : Z.t list }
  | Generated of generated
  | Table of table

and literal_check = { method_ : Path.t; subject : literal_subject; clauses : int list }

and literal_subject =
  | Template_text of string list
  | Constant_argument of { definition : Path.t; origin : int }

and generated =
  | Entry of impl_method
  | Any_entry of impl_method
  | Locked_entry of { capability : Path.t; name : string }
  | Adapter of {
      function_ : Path.t;
      type_arguments : Ground.argument list;
      ty : Ground.function_type;
    }
  | Program_main of Path.t

and table =
  | Impl_table of { impl : Path.t; type_arguments : Ground.argument list }
  | Any_table of { impl : Path.t; type_arguments : Ground.argument list }
  | Locked_table of Path.t

and impl_method = {
  impl : Path.t;
  name : string;
  receiver : Path.receiver;
  type_arguments : Ground.argument list;
}

type t = key

val make_method_path : impl_method -> Path.t
val compare : key -> key -> int
val equal : key -> key -> bool
val hash : key -> int
val make_symbol : key -> string
val mangle_path : Path.t -> string
val make_type_symbol : Ground.ty -> string
val to_string : key -> string
