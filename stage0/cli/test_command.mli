type test = { path : Path.t; module_ : Path.module_; name : string; file : string; line : int }

val select : Project.t -> paths:string list -> match_:string option -> test list
val label : test -> string
val duration : int -> string

type timings = { check : int; build : int; tests : int; total : int }

type progress = {
  line : Status_line.t;
  tests : test array;
  mutable ended : int;
  mutable not_passed : int;
  mutable running_since : int option;
  running : (int, int) Hashtbl.t;
}

val run :
  directory:string ->
  paths:string list ->
  match_:string option ->
  timings:bool ->
  rerun:bool ->
  json:bool ->
  sanitize:bool ->
  int
