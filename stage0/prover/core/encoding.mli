val find_bounds : Types.ty -> (Z.t * Z.t) option
val find_float_format : Types.ty -> (int * int) option
val make_constructor_symbol : Types.ty -> string option -> 'a Logic.Symbol.t
val is_standard_equal : Path.t -> bool

val find_visible_type :
  State.environment -> Types.ty -> (Types.type_interface * Types.substitution) option

val find_constructors :
  State.environment -> Types.ty -> (string option * (string * Types.ty) list) list option

val sort_of : Types.ty -> Logic.sort
val sequence_path : Path.t
val make_sequence_type : Types.ty -> Types.ty

val list_constructors :
  State.environment -> Types.ty -> (Logic.symbol * (Logic.symbol * Logic.sort) list) list option

val is_equality_identity : State.environment -> ?seen:Types.ty list -> Types.ty -> bool
val make_in_range : Types.ty -> Logic.term -> Logic.term

val make_in_values :
  Types.ty -> Logic.term -> low:Logic.term -> high:Logic.term -> inclusive:bool -> Logic.term

val count_values : Types.ty -> low:Logic.term -> high:Logic.term -> inclusive:bool -> Logic.term
val offset_value : Types.ty -> low:Logic.term -> Logic.term -> Logic.term
val arrive : State.frame -> string -> Types.ty -> Logic.term

val list_definition_bounds :
  Lookups.t -> current:Path.t -> condition:Types.condition -> Interface.Impls.bounds

val substitute_declared_type : State.frame -> Types.ty -> Types.ty
val substitute_type : State.frame -> Types.ty -> Types.ty
val find_local_type : State.frame -> Locals.key -> Types.ty option

val find_impl :
  State.environment -> Types.trait_reference -> Types.ty -> (Path.t * Types.substitution) option

val select_field :
  State.environment -> Types.ty -> string option -> string -> Logic.term -> Logic.term

val replace_field :
  State.environment -> Types.ty -> string option -> string -> Logic.term -> Logic.term -> Logic.term

val find_root : State.frame -> Locals.local -> (Types.ty * Logic.term) option
val find_changed_part : State.frame -> State.changed_part -> (Types.ty * Logic.term) option

val replace_part :
  State.environment ->
  Types.ty ->
  Logic.term ->
  string list ->
  (Types.ty -> Logic.term -> Logic.term) ->
  Logic.term option
