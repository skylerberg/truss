val run_ghost_code : State.context -> State.frame -> Mir.t -> Logic.term

val assume_extensional :
  State.context -> State.frame -> Types.ty -> Logic.term -> Logic.term -> unit

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
  literals:string list ->
  Logic.term ->
  State.frame * Logic.term

val apply_map_literal :
  State.context ->
  State.frame ->
  ty:Types.ty ->
  location:Obligation.location ->
  (int option * Logic.term * Logic.term) list ->
  State.frame * Logic.term

val make_text_value : State.context -> State.frame -> Types.ty -> string -> Logic.term

val make_owner_of_view :
  State.context -> State.frame -> view:Types.ty -> owner:Types.ty -> Logic.term -> Logic.term

val project_field :
  State.context ->
  State.frame ->
  Types.ty ->
  string option ->
  string ->
  Types.ty ->
  Logic.term ->
  Logic.term

val translate_global_value :
  State.context ->
  State.frame ->
  Invocation.site ->
  Path.t ->
  Types.argument list ->
  is_argument:bool ->
  Logic.term

val evaluate_constant : State.context -> State.frame -> Path.t -> Logic.term

val apply_construct :
  State.context ->
  State.frame ->
  Invocation.site ->
  string option ->
  (string * Logic.term option) list ->
  State.frame * Logic.term

val make_text_match :
  State.context -> Obligation.location -> Types.ty -> Logic.term -> string -> Logic.term

val apply_specification_function :
  State.context ->
  State.frame ->
  location:Obligation.location ->
  Core.specification_function ->
  Logic.term list ->
  unconverted:Types.ty list ->
  types:Types.ty list ->
  State.frame * Logic.term

val copy_value :
  ?literal:string -> State.context -> State.frame -> Types.ty -> Logic.term -> State.frame
