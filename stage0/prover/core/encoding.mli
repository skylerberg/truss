val find_bounds : Types.ty -> (Z.t * Z.t) option
val find_float_format : Types.ty -> (int * int) option
val make_constructor_symbol : Types.ty -> string option -> 'a Logic.Symbol.t
val make_selector_symbol : Types.ty -> string option -> string -> 'a Logic.Symbol.t
val is_standard_equal : Path.t -> bool

val find_visible_type :
  State.context -> Types.ty -> (Types.type_interface * Types.substitution) option

val find_constructors :
  State.context -> Types.ty -> (string option * (string * Types.ty) list) list option

val declare_sort : State.context -> Types.ty -> Logic.sort
val is_equality_identity : State.context -> ?seen:Types.ty list -> Types.ty -> bool
val make_in_range : Types.ty -> Logic.term -> Logic.term

val make_in_values :
  Types.ty -> Logic.term -> low:Logic.term -> high:Logic.term -> inclusive:bool -> Logic.term

val count_values : Types.ty -> low:Logic.term -> high:Logic.term -> inclusive:bool -> Logic.term
val offset_value : Types.ty -> low:Logic.term -> Logic.term -> Logic.term
val arrive : State.context -> State.frame -> string -> Types.ty -> Logic.term

val list_definition_bounds :
  Lookups.t -> current:Path.t -> condition:Types.condition -> Interface.Impls.bounds

val substitute_declared_type : State.context -> State.frame -> Types.ty -> Types.ty
val substitute_type : State.context -> State.frame -> Types.ty -> Types.ty
val find_local_type : State.context -> State.frame -> Locals.key -> Types.ty option

val find_impl :
  State.context -> Types.trait_reference -> Types.ty -> (Path.t * Types.substitution) option

val select_field : State.context -> Types.ty -> string option -> string -> Logic.term -> Logic.term

val replace_field :
  State.context -> Types.ty -> string option -> string -> Logic.term -> Logic.term -> Logic.term

val find_root : State.context -> State.frame -> Locals.local -> (Types.ty * Logic.term) option

val find_changed_part :
  State.context -> State.frame -> State.changed_part -> (Types.ty * Logic.term) option

val replace_part :
  State.context ->
  Types.ty ->
  Logic.term ->
  string list ->
  (Types.ty -> Logic.term -> Logic.term) ->
  Logic.term option
