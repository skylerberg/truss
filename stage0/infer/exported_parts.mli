module Names = Resolve.Names
module Environment = Interface.Environment

val check : State.state -> State.Environment.lowered_interface -> unit
