type overload =
  | Type_overload of Path.t
  | List_overload of Path.t
  | Trait_overload of Types.trait_reference * Types.trait_method

val classify_receiver_mode : Syntax.argument list -> Language.Mode.t
val make_method_owner : State.state -> Types.ty -> Catalog.Inference.method_owner
val check_name : State.state -> State.env -> Syntax.expression -> Resolve.head -> Types.ty
val check_field : State.state -> Syntax.expression -> Types.ty -> Syntax.name -> Types.ty

val check_static_member :
  State.state -> ?expected:Types.ty -> Syntax.expression -> Types.ty -> Syntax.name -> Types.ty

val check_trait_value_in_full :
  State.state ->
  ?expected:Types.ty ->
  Syntax.expression ->
  Path.t ->
  trait_arguments:Types.argument list option ->
  Syntax.name ->
  Types.ty

val resolve_member_overloads :
  State.state ->
  Types.ty ->
  string ->
  ((Path.receiver * overload) list Resolve.Names.lookup, Types.trait_reference list) Result.t

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

val find_method_of_an_unmet_impl :
  State.state ->
  Types.ty ->
  string ->
  Path.receiver ->
  (Types.trait_reference * Types.trait_method) option

val has_method_without_self : State.state -> Types.ty -> string -> bool

val instantiate_trait_method :
  State.state ->
  written:Syntax.id ->
  self_type:Types.ty ->
  Types.trait_reference ->
  Types.trait_method ->
  Instantiation.instance * Tables.trait_method

val has_sealed_method : State.state -> Types.ty -> string -> bool

val find_sealed_provider :
  State.state -> Types.ty -> Types.trait_reference -> Types.trait_reference option

val resolve_overloads :
  State.state ->
  Types.ty ->
  string ->
  ((Path.receiver * overload) list Resolve.Names.lookup, Types.trait_reference list) Result.t
