type t = { setup : (Mir.local * Types.ty * Mir.call) list; call : Mir.call }

val forward_call :
  substitution:Types.substitution ->
  fresh:(unit -> Mir.local) ->
  Mir.Graph.t ->
  Mir.call ->
  t option
