val record : Nodes.t -> unit

type saved_node = {
  saved_name : string;
  saved_key : string;
  saved_value : string option;
  saved_reads : int list;
  saved_root : bool;
  saved_stored : bool;
  saved_opaque : bool;
}

type artifact = {
  base : string option;
  saved : saved_node list;
  table : (string * string) array;
  collected : (string * string) list;
  whole_size : int;
  difference_size : int;
  difference_count : int;
}

val write : ?full:bool -> Nodes.t -> string

type debt = { whole : int; differences : int; depth : int }

val debt : Nodes.t -> debt
val artifact : Nodes.t -> string option
val unwritten : Nodes.t -> bool
val values_in : Nodes.store -> string -> string list
val forget_bases : unit -> unit
val frozen_of : Nodes.store -> bases:Nodes.t list -> fixed:bool -> string -> Nodes.t option
val open_ : ?log:bool -> Nodes.store -> bases:Nodes.t list -> string -> Nodes.t option
