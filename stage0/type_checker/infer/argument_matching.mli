type owner = Catalog.Inference.owner

type site =
  | Call
  | Construction of owner
  | Tuple_construction of owner
  | Pattern of { owner : owner; is_tuple_type : bool }

type entry = { label : Syntax.name option; punned : string option; origin : Core.origin }

val list_indexes :
  State.state -> site -> parameter_names:string list -> entry list -> (int, Types.ty) result list

val find_labeled_form :
  parameter_names:string list -> entry list -> (string option * Core.origin) list option

val find_owner : site -> owner option
