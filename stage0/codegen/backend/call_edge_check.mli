val check :
  Interface.Lookups.t ->
  find_call_edges:(Path.t -> Path.t list option) ->
  Instance.key ->
  Emit_c.fragment ->
  unit
