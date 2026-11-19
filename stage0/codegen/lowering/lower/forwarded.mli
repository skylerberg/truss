type t = { setup : (Mir.local * Types.ty * Mir.call) list; call : Mir.call }

val forward_call :
  substitution:Types.substitution ->
  make_fresh_local:(unit -> Mir.local) ->
  Mir.Graph.t ->
  Mir.call ->
  t option
