(** Values built and named: literals, constructors, constants, named functions, and templates. *)

val ghost_code : State.context -> State.frame -> Mir.t -> Logic.term
val extensional : State.context -> State.frame -> Types.ty -> Logic.term -> Logic.term -> unit

val apply_list_literal :
  State.context -> State.frame -> Invocation.site -> Logic.term list -> State.frame * Logic.term

val apply_template :
  State.context ->
  State.frame ->
  Invocation.site ->
  trait:Types.trait_reference ->
  name:string ->
  receiver:Path.receiver ->
  evidence:Core.evidence ->
  texts:string list ->
  Logic.term ->
  State.frame * Logic.term

val apply_map_literal :
  State.context ->
  State.frame ->
  ty:Types.ty ->
  span:State.span ->
  (int option * Logic.term * Logic.term) list ->
  State.frame * Logic.term

val text_value : State.context -> State.frame -> Types.ty -> string -> Logic.term
val cursor_trait : Path.t
val option_path : Path.t
val some_parts : State.context -> State.frame -> Types.ty -> Logic.term

val field_of :
  State.context ->
  State.frame ->
  Types.ty ->
  string option ->
  string ->
  Types.ty ->
  Logic.term ->
  Logic.term

val global_value :
  State.context ->
  State.frame ->
  Invocation.site ->
  Path.t ->
  Types.argument list ->
  is_argument:bool ->
  Logic.term

val constant_type : State.context -> Path.t -> Types.ty
val constant_value : State.context -> State.frame -> Path.t -> Logic.term

val apply_construct :
  State.context ->
  State.frame ->
  Invocation.site ->
  string option ->
  (string * Logic.term option) list ->
  State.frame * Logic.term

val text_matches : State.context -> State.span -> Types.ty -> Logic.term -> string -> Logic.term

val apply_specification_function :
  State.context ->
  State.frame ->
  span:State.span ->
  Core.specification_function ->
  Logic.term list ->
  unconverted:Types.ty list ->
  types:Types.ty list ->
  State.frame * Logic.term

val copied : State.context -> State.frame -> Types.ty -> Logic.term -> State.frame
