type verdict = Moves | Reads | Refused of (Context.context -> Syntax.span -> Types.ty -> unit)

val verdict :
  Context.context -> Place.t -> type_:Types.ty -> is_returned:bool -> is_captured:bool -> verdict

val copy_fix :
  Context.context -> string -> Types.ty -> Syntax.span -> Syntax.span Diagnostic.fix list

val analyse : Context.context -> Mir.Graph.body -> Moves.t

val check :
  Context.context ->
  Mir.Graph.t ->
  moves:(Mir.Graph.body -> Moves.t) ->
  returns_to_caller:bool ->
  unit
