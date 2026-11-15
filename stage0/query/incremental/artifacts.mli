val record_facts : Nodes.t -> unit
val write : ?full:bool -> ?stores_every_value:bool -> Nodes.t -> string
val chain_size : Nodes.t -> Nodes.chain_size
val artifact : Nodes.t -> string option
val unwritten : Nodes.t -> bool
val values_in : Nodes.store -> string -> string list
val forget_bases : unit -> unit
val frozen_of : Nodes.store -> bases:Nodes.t list -> fixed:bool -> string -> Nodes.t option
val open_ : ?log:bool -> Nodes.store -> bases:Nodes.t list -> string -> Nodes.t option
