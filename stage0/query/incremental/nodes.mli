exception Cycle of string list
exception Lost of string

type subject = { path : Path.t; part : string option }

type counters = {
  marked : int;
  confirmed : int;
  computed : int;
  changed : int;
  adopted : int;
  copied : int;
  collected : int;
}

type tally = {
  mutable marks : int;
  mutable confirmations : int;
  mutable computations : int;
  mutable changes : int;
  mutable adoptions : int;
  mutable copies : int;
  mutable collections : int;
}

type store = {
  id : string;
  version : string;
  put : string -> string;
  get : string -> string option;
  find : kind:string -> key:string -> string option;
  add : kind:string -> key:string -> string -> unit;
}

val phases : int

type t = {
  id : int;
  bases : t list;
  mutable frozen : bool;
  mutable fixed : bool;
  tables : (int, binding) Hashtbl.t;
  own : (int, node) Hashtbl.t;
  foreign : (int, (int, node) Hashtbl.t) Hashtbl.t;
  shadows : (int, node) Hashtbl.t;
  mutable clock : int;
  mutable frames : frame list;
  seeds : node list array;
  marks : node list array;
  mutable waiting : int;
  mutable candidates : node list;
  logging : bool;
  log : node Dynarray.t;
  computed : node Dynarray.t;
  changed : node Dynarray.t;
  tally : tally;
  mutable store : store option;
  unsaved : (int, node) Hashtbl.t;
  mutable collected : (string * string) list;
  mutable chain : string option;
  mutable on_whole : bool;
  mutable whole : int;
  mutable differences : int;
  mutable depth : int;
  mutable activity : int;
  mutable audited : int;
}

and binding = Binding : 'table Type.Id.t * 'table -> binding

and node = {
  id : int;
  engine : t;
  phase : int;
  below : node option;
  mutable cell : cell;
  mutable reads : node list;
  readers : (int, node) Hashtbl.t;
  mutable marked : bool;
  mutable busy : bool;
  mutable changed_at : int;
  mutable verified_at : int;
  mutable root : bool;
  mutable alive : bool;
  mutable fingerprint : fingerprint;
  mutable identity : string option;
  mutable written : written;
}

and written = Unwritten | In_whole | In_difference
and fingerprint = Unknown | Hashed of { hash : string; stored : bool } | Opaque of string

and cell =
  | Input : ('key, 'value) input * ('key, 'value) input_cell -> cell
  | Result : ('key, 'value) query * ('key, 'value) result_cell -> cell
  | Unfilled

and ('key, 'value) input = {
  input_number : int;
  input_name : string;
  input_show : 'key -> string;
  input_equal : 'value -> 'value -> bool;
  input_about : 'key -> subject option;
  input_cells : ('key, ('key, 'value) input_cell) Hashtbl.t Type.Id.t;
}

and ('key, 'value) input_cell = { input_key : 'key; input_node : node; mutable slot : 'value slot }
and 'value slot = Unset | Set of 'value | Stored

and ('key, 'value) query = {
  number : int;
  name : string;
  show : 'key -> string;
  phase : int;
  saved : bool;
  portable : bool;
  equal : 'value -> 'value -> bool;
  about : 'key -> subject option;
  compute : context -> 'key -> 'value;
  cells : ('key, ('key, 'value) result_cell) Hashtbl.t Type.Id.t;
}

and ('key, 'value) result_cell = {
  key : 'key;
  node : node;
  mutable outcome : 'value outcome option;
}

and 'value outcome = Value of 'value | Raised of exn

and frame = {
  owner : node;
  read : node Dynarray.t;
  seen : (int, unit) Hashtbl.t;
  mutable cyclic : string list option;
}

and context = { engine : t; frame : frame option; observing : bool }

type ('key, 'value) cells = ('key, ('key, 'value) result_cell) Hashtbl.t
type ('key, 'value) input_cells = ('key, ('key, 'value) input_cell) Hashtbl.t

val numbers : int ref
val seal : unit -> unit
val check_not_sealed : string -> unit
val auditing : bool ref
val remembered : t Weak.t ref
val within_audit : bool ref
val create : ?log:bool -> ?bases:t list -> unit -> t
val hash_of : fingerprint -> string option
val context : t -> context
val observer : t -> context
val engine_of : context -> t
val attach : t -> store -> unit
val counters : t -> counters
val tick : t -> int
val name : node -> string
val label : node -> string
val subject : node -> subject option
val is_input : node -> bool
val is_fixed : node -> bool
val bytes_of : 'a -> string
val key_bytes : node -> string
val identity : node -> string
val find_table : t -> int -> 'table Type.Id.t -> 'table option
val result_cells : t -> ('key, 'value) query -> ('key, 'value) cells
val input_cells : t -> ('key, 'value) input -> ('key, 'value) input_cells
val find_result : t -> ('key, 'value) query -> 'key -> ('key, 'value) result_cell option
val find_input : t -> ('key, 'value) input -> 'key -> ('key, 'value) input_cell option

val make_result :
  t -> ('key, 'value) query -> 'key -> below:node option -> ('key, 'value) result_cell

val make_input : t -> ('key, 'value) input -> 'key -> below:node option -> ('key, 'value) input_cell
val add_reader : t -> node -> node -> unit
val remove_reader : t -> node -> node -> unit
