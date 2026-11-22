type t =
  | Code of { path : Path.t; instantiation : Ground.instantiation; assumes_condition : bool }
  | Constant of Path.t
  | Drop of Ground.ty
  | Copy of Ground.ty
  | Debug of Ground.ty
  | Any_drop of Ground.ty
  | Any_copy of Ground.ty
  | Encode of Ground.ty
  | Evaluator of Path.t
  | Assertion of { definition : Path.t; condition : int }
  | Call_evaluation of { function_ : Path.t; arguments : Z.t list }
  | Generated of generated
  | Table of table

and generated =
  | Entry of impl_method
  | Any_entry of impl_method
  | Locked_entry of { capability : Path.t; name : string }
  | Adapter of {
      function_ : Path.t;
      instantiation : Ground.instantiation;
      ty : Ground.function_type;
    }
  | Program_main of Path.t
  | Test_main of Path.t

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

val make_method_path : impl_method -> Path.t
val make_code : Path.t -> Ground.instantiation -> t
val make_method_code : impl_method -> t
val compare : t -> t -> int
val equal : t -> t -> bool
val hash : t -> int
val to_string : t -> string
