type t = Amortized | Metric of Metric.t | Calls | O | Potential | By | Bit_vector

val spellings : (string * t) list
val of_token : Token.kind -> t option
val resources : t list

val expect :
  ?suggested:t list -> Cursor.t -> accepted:t list -> category:string -> expected:string -> t
