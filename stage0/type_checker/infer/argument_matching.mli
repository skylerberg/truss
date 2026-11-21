type site =
  | Call
  | Construction of string
  | Tuple_construction of string
  | Pattern of { owner : string; is_tuple_type : bool }

type entry = { label : Syntax.name option; punned : string option; span : Source.Definition_span.t }

val list_indexes :
  State.state -> site -> parameter_names:string list -> entry list -> (int, Types.ty) result list

val find_labeled_form : State.state -> parameter_names:string list -> entry list -> string option
val find_owner : site -> string option
val show_names : string list -> string
