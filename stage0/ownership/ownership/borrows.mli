val check :
  Context.context ->
  read_moves:(Mir.Graph.body -> Moves.t) ->
  returns_to_caller:bool ->
  Mir.Graph.t ->
  unit
