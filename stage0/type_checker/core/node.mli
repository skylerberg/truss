type t = private int
type counter

val create_counter : unit -> counter
val allocate : counter -> t
