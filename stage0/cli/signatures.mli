val text : Query.context -> body:bool -> opaque:bool -> Resolve.Names.key -> string option
val kind_word : Resolve.Names.kind -> string

val parts : string list
(** The parts of a definition that its dependents read. *)

val of_path : Query.context -> Path.t -> string option
(** The signature of the definition at a path. *)

val labeled : string -> string -> string
(** A signature after a label, as in [    was: fn f()], with each later line indented to align with
    the first. *)
