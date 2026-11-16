type test = { path : Path.t; module_ : Path.module_; name : string; file : string; line : int }

val select :
  Workspace.snapshot ->
  Database.t ->
  Path.package list ->
  paths:string list ->
  match_:string option ->
  test list

val label_test : test -> string

val run_tests :
  ?rerun:bool ->
  ?report_progress:(Compile.progress -> unit) ->
  Database.t ->
  Workspace.snapshot ->
  Path.package list ->
  test list ->
  Compile.record list

val run : paths:string list -> match_:string option -> timings:bool -> rerun:bool -> int

module For_testing : sig
  val show_duration : int -> string
end
