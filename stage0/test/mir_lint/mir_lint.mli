val list_place_locals : Mir.place -> Mir.local list
val list_operand_locals : Mir.operand -> Mir.local list
val check : string -> Mir.Graph.body -> unit
val check_file : Database.t -> Path.file -> unit
