type verdict =
  | Moves
  | Reads
  | Refused of (Context.context -> Source.Definition_span.t -> Types.ty -> unit)

val decide_move :
  Context.context -> Place.t -> type_:Types.ty -> is_returned:bool -> is_captured:bool -> verdict

val copy_fix :
  Context.context ->
  string ->
  Types.ty ->
  Source.Definition_span.t ->
  Source.Definition_span.t Diagnostic.fix list

val analyse : Context.context -> Mir.Graph.body -> Moves.t

val check :
  Context.context ->
  Mir.Graph.t ->
  read_moves:(Mir.Graph.body -> Moves.t) ->
  returns_to_caller:bool ->
  unit
