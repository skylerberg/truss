type entry = {
  name : Path.package;
  version : Version.t;
  hash : string;
  holds : Grant.capability list;
}

type t = entry list

exception Malformed of { line : int; problem : Project_catalog.Problem.lock }

val parse : string -> t
val print : t -> string
val find : t -> Path.package -> entry option
