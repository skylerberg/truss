val check :
  Interface.Lookups.t ->
  find_call_edges:(Path.t -> Path.t list option) ->
  Lowered.Item.t ->
  Emit_c.fragment ->
  unit
