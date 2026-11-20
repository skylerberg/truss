type overload =
  | Type_overload of Path.t
  | View_overload of Path.t
  | Trait_overload of Types.trait_reference * Types.trait_method

val classify_receiver_mode : Syntax.argument list -> Language.Mode.t
val describe_missing_method : State.state -> Types.ty -> string -> string
val check_name : State.state -> State.env -> Syntax.expression -> Resolve.head -> Types.ty
val check_field : State.state -> Syntax.expression -> Types.ty -> Syntax.name -> Types.ty
val check_static_member : State.state -> Syntax.expression -> Types.ty -> Syntax.name -> Types.ty

val check_explicit_type_arguments :
  ?head:int ->
  State.state ->
  Syntax.expression ->
  Instantiation.instance ->
  Syntax.bracket_item list ->
  (unit, Types.ty) result

val finish_call :
  State.state ->
  State.env ->
  Syntax.expression ->
  Path.t ->
  Tables.callee ->
  Instantiation.instance ->
  Tables.argument list ->
  string list ->
  Types.ty

val lookup_trait_static_methods :
  State.state ->
  Path.t ->
  string ->
  (Types.trait_reference * Types.trait_method) list Resolve.Names.lookup

val instantiate_trait_method :
  State.state ->
  written:Syntax.id ->
  self_type:Types.ty ->
  Types.trait_reference ->
  Types.trait_method ->
  Instantiation.instance * Tables.callee

val has_sealed_method : State.state -> Types.ty -> string -> bool

val find_sealed_provider :
  State.state -> Types.ty -> Types.trait_reference -> Types.trait_reference option

val resolve_overloads :
  State.state ->
  Types.ty ->
  string ->
  ((Path.receiver * overload) list Resolve.Names.lookup, Types.trait_reference list) Result.t

val find_elements_calls :
  State.state ->
  cause:State.cause ->
  Syntax.expression ->
  Types.ty ->
  Language.Mode.t ->
  (Tables.loop * Types.ty * Language.Mode.t) Resolve.Names.lookup

val find_consuming_cursor :
  State.state -> Syntax.expression -> Types.ty -> (Tables.loop * Types.ty) Resolve.Names.lookup

val find_remaining_call : State.state -> Types.ty -> (Types.condition * Tables.call) option
