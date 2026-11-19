val lower_for_each :
  Lowering.state ->
  schedule:Lowering.schedule ->
  iteration:Mir.iteration ->
  each:(Lowered.place -> unit) ->
  origin:Core.origin ->
  unit
