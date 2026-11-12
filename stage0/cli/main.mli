val evaluate : string list -> Outcome.t

type request = {
  arguments : string list;
  directory : string;
  registry : string option;
  terminal : bool;
  columns : int option;
}

type response = { output : string; outcome : Outcome.t }

val serve : string -> unit
val client : string list -> int
