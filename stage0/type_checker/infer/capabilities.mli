type capability_use = { capabilities : Types.capability_set; callee : Path.t option }

val check :
  State.state -> Interface.Environment.elaborated_interface -> Core.t -> capability_use list
