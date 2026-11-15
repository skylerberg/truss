type t = { types : Ground.ty list; folded_constants : Path.t list }

val of_instance : Definitions.context -> Instance.key -> t
