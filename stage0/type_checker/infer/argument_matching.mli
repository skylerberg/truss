type site =
  | Call
  | Construction of { owner : string; declared_order : string list Lazy.t }
  | Tuple_construction of string
  | Pattern of { owner : string; declared_order : string list Lazy.t; is_tuple_type : bool }

type entry = { label : Syntax.name option; punned : string option; span : Source.Definition_span.t }

val list_indexes :
  State.state -> site -> parameter_names:string list -> entry list -> (int, Types.ty) result list

val find_labeled_form :
  State.state ->
  parameter_names:string list ->
  declared_order:string list Lazy.t ->
  entry list ->
  string option

val find_owner : site -> string option
val show_names : string list -> string
