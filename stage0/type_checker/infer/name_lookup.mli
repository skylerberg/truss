type overload =
  | Type_overload of Path.t
  | View_overload of Path.t
  | Trait_overload of Types.trait_reference * Types.trait_method

val classify_receiver : Syntax.expression -> Path.receiver
val describe_missing_method : State.state -> Types.ty -> string -> string

val coerce :
  State.state ->
  State.env ->
  ?argument:Types.mode ->
  Syntax.expression ->
  actual:Types.ty ->
  expected:Types.ty ->
  unit

val infer_literal_type : State.state -> expected:Types.ty option -> Types.literal_kind -> Types.ty
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

val resolve_evidence : State.state -> Syntax.expression -> Types.ty -> Types.trait_reference -> unit

val instantiate_trait_method :
  State.state ->
  Source.Definition_span.t ->
  self_type:Types.ty ->
  Types.trait_reference ->
  Types.trait_method ->
  evidence:Tables.evidence ->
  Instantiation.instance * Tables.callee

val resolve_overloads :
  State.state ->
  Types.ty ->
  string ->
  ((Path.receiver * overload) list Resolve.Names.lookup, Types.trait_reference list) Result.t

val find_elements_calls :
  State.state ->
  Source.Definition_span.t ->
  Types.ty ->
  Types.mode ->
  (Tables.loop * Types.ty * Types.mode) Resolve.Names.lookup

val find_consuming_cursor :
  State.state ->
  Source.Definition_span.t ->
  Types.ty ->
  (Tables.loop * Types.ty) Resolve.Names.lookup

val find_remaining_call : State.state -> Source.Definition_span.t -> Types.ty -> Tables.call option
