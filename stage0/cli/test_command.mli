type test = { path : Path.t; module_ : Path.module_; name : string; file : string; line : int }

val select : Project.t -> paths:string list -> match_:string option -> test list
val label : test -> string

val run_tests :
  ?rerun:bool ->
  ?progress:(Compile.progress -> unit) ->
  Project.t ->
  test list ->
  Compile.record list

val run : paths:string list -> match_:string option -> timings:bool -> rerun:bool -> int

module For_testing : sig
  val duration : int -> string
end
