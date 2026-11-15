type t

val variable : string
val current : unit -> t option
val versions : t -> Path.package -> (Version.t * string) list
val newest : t -> Path.package -> (Version.t * string) option
val hash_of : t -> Path.package -> Version.t -> string option
val add : t -> Path.package -> Version.t -> (string * string) list -> unit
val fetch : t -> into:string -> Path.package -> Version.t -> hash:string -> (string, string) result
