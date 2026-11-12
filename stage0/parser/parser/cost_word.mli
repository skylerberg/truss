type t = Amortized | Time | Allocations | Allocated_bytes | Calls | O | Finite | Potential

val spellings : (string * t) list
val of_token : Token.kind -> t option
val resources : t list
val expect : ?suggested:t list -> Cursor.t -> accepted:t list -> what:string -> expected:string -> t
