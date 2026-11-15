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

let phases = 16

type chain_size = { whole : int; differences : int; depth : int }

type t = {
  id : int;
  bases : t list;
  mutable frozen : bool;
  mutable fixed : bool;
  tables : (int, binding) Hashtbl.t;
  own : (int, node) Hashtbl.t;
  readers_of_base_nodes : (int, (int, node) Hashtbl.t) Hashtbl.t;
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
  unwritten_nodes : (int, node) Hashtbl.t;
  mutable collected : (string * string) list;
  mutable chain : string option;
  mutable on_whole : bool;
  mutable chain_size : chain_size;
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

let engines = ref 0
let nodes_made = ref 0
let numbers = ref 0
let sealed = ref false
let seal () = sealed := true

let check_not_sealed name =
  if !sealed then
    invalid_arg
      (Printf.sprintf
         "Incremental: `%s` is declared after a state was opened; declare it when its module is \
          initialized"
         name)

let auditing = ref false
let remembered : t Weak.t ref = ref (Weak.create 16)
let remembered_count = ref 0
let within_audit = ref false

let remember engine =
  if !auditing && not !within_audit then begin
    if !remembered_count = Weak.length !remembered then begin
      let live = ref [] in
      for index = 0 to Weak.length !remembered - 1 do
        match Weak.get !remembered index with Some engine -> live := engine :: !live | None -> ()
      done;
      let live = List.rev !live in
      let grown = Weak.create (max 16 (2 * (List.length live + 1))) in
      List.iteri (fun index engine -> Weak.set grown index (Some engine)) live;
      remembered := grown;
      remembered_count := List.length live
    end;
    Weak.set !remembered !remembered_count (Some engine);
    incr remembered_count
  end

let create ?(log = false) ?(bases = []) () =
  List.iter
    (fun base ->
      if not base.frozen then invalid_arg "Incremental.create: a base that is not frozen")
    bases;
  let all =
    List.fold_left
      (fun distinct base -> if List.memq base distinct then distinct else distinct @ [ base ])
      []
      (bases @ List.concat_map (fun base -> base.bases) bases)
  in
  incr engines;
  let engine =
    {
      id = !engines;
      bases = all;
      frozen = false;
      fixed = false;
      tables = Hashtbl.create 64;
      own = Hashtbl.create 1024;
      readers_of_base_nodes = Hashtbl.create 64;
      shadows = Hashtbl.create 64;
      clock = 1;
      frames = [];
      seeds = Array.make phases [];
      marks = Array.make phases [];
      waiting = 0;
      candidates = [];
      logging = log;
      log = Dynarray.create ();
      computed = Dynarray.create ();
      changed = Dynarray.create ();
      tally =
        {
          marks = 0;
          confirmations = 0;
          computations = 0;
          changes = 0;
          adoptions = 0;
          copies = 0;
          collections = 0;
        };
      store = List.find_map (fun base -> base.store) all;
      unwritten_nodes = Hashtbl.create 256;
      collected = [];
      chain = None;
      on_whole = false;
      chain_size = { whole = 0; differences = 0; depth = 0 };
      activity = 0;
      audited = 0;
    }
  in
  remember engine;
  engine

let hash_of = function
  | Unknown -> None
  | Hashed { hash; _ } -> Some hash
  | Opaque nonce -> Some nonce

let context engine = { engine; frame = None; observing = false }
let observer engine = { engine; frame = None; observing = true }
let engine_of (context : context) = context.engine
let attach engine store = engine.store <- Some store

let counters engine =
  {
    marked = engine.tally.marks;
    confirmed = engine.tally.confirmations;
    computed = engine.tally.computations;
    changed = engine.tally.changes;
    adopted = engine.tally.adoptions;
    copied = engine.tally.copies;
    collected = engine.tally.collections;
  }

let tick engine =
  engine.clock <- engine.clock + 1;
  engine.clock

let name (node : node) =
  match node.cell with
  | Input (input, _) -> input.input_name
  | Result (query, _) -> query.name
  | Unfilled -> "?"

let label (node : node) =
  match node.cell with
  | Input (input, cell) ->
      Printf.sprintf "%s(%s)" input.input_name (input.input_show cell.input_key)
  | Result (query, cell) -> Printf.sprintf "%s(%s)" query.name (query.show cell.key)
  | Unfilled -> "?"

let subject (node : node) =
  match node.cell with
  | Input (input, cell) -> input.input_about cell.input_key
  | Result (query, cell) -> query.about cell.key
  | Unfilled -> None

let is_input (node : node) = match node.cell with Input _ -> true | Result _ | Unfilled -> false
let is_fixed (node : node) = node.engine.fixed
let bytes_of value = Marshal.to_string value [ Marshal.No_sharing ]

let key_bytes (node : node) =
  match node.cell with
  | Input (_, cell) -> bytes_of cell.input_key
  | Result (_, cell) -> bytes_of cell.key
  | Unfilled -> ""

let derive_identity = Blake3.derive_key ~context:"truss 2026-11-12 incremental node identity"

let identity (node : node) =
  match node.identity with
  | Some identity -> identity
  | None ->
      let identity =
        derive_identity
          (Cbor.encode (Cbor.Array [ Cbor.Text (name node); Cbor.Bytes (key_bytes node) ]))
      in
      node.identity <- Some identity;
      identity

let new_node engine ~phase ~below =
  incr nodes_made;
  let node =
    {
      id = !nodes_made;
      engine;
      phase;
      below;
      cell = Unfilled;
      reads = [];
      readers = Hashtbl.create 1;
      marked = false;
      busy = false;
      changed_at = 0;
      verified_at = 0;
      root = false;
      alive = true;
      fingerprint = Unknown;
      identity = None;
      written = Unwritten;
    }
  in
  Hashtbl.replace engine.own node.id node;
  node

let find_table : type table. t -> int -> table Type.Id.t -> table option =
 fun engine number id ->
  match Hashtbl.find_opt engine.tables number with
  | None -> None
  | Some (Binding (other, table)) -> (
      match Type.Id.provably_equal id other with
      | Some Type.Equal -> Some table
      | None -> invalid_arg "Incremental: two declarations share a number")

let own_table : type table. t -> int -> table Type.Id.t -> (unit -> table) -> table =
 fun engine number id make ->
  match find_table engine number id with
  | Some table -> table
  | None ->
      let table = make () in
      Hashtbl.replace engine.tables number (Binding (id, table));
      table

let result_cells engine (query : ('key, 'value) query) : ('key, 'value) cells =
  own_table engine query.number query.cells (fun () -> Hashtbl.create 64)

let input_cells engine (input : ('key, 'value) input) : ('key, 'value) input_cells =
  own_table engine input.input_number input.input_cells (fun () -> Hashtbl.create 64)

let find_result engine (query : ('key, 'value) query) (key : 'key) =
  let look engine =
    match find_table engine query.number query.cells with
    | Some table -> Hashtbl.find_opt table key
    | None -> None
  in
  match look engine with Some cell -> Some cell | None -> List.find_map look engine.bases

let find_input engine (input : ('key, 'value) input) (key : 'key) =
  let look engine =
    match find_table engine input.input_number input.input_cells with
    | Some table -> Hashtbl.find_opt table key
    | None -> None
  in
  match look engine with Some cell -> Some cell | None -> List.find_map look engine.bases

let make_result engine (query : ('key, 'value) query) key ~below =
  let node = new_node engine ~phase:query.phase ~below in
  let cell = { key; node; outcome = None } in
  node.cell <- Result (query, cell);
  Hashtbl.replace (result_cells engine query) key cell;
  cell

let make_input engine (input : ('key, 'value) input) key ~below =
  let node = new_node engine ~phase:0 ~below in
  let cell = { input_key = key; input_node = node; slot = Unset } in
  node.cell <- Input (input, cell);
  Hashtbl.replace (input_cells engine input) key cell;
  cell

let add_reader engine (read : node) (reader : node) =
  if read.engine == engine then Hashtbl.replace read.readers reader.id reader
  else
    let table =
      match Hashtbl.find_opt engine.readers_of_base_nodes read.id with
      | Some table -> table
      | None ->
          let table = Hashtbl.create 2 in
          Hashtbl.replace engine.readers_of_base_nodes read.id table;
          table
    in
    Hashtbl.replace table reader.id reader

let remove_reader engine (read : node) (reader : node) =
  if read.engine == engine then Hashtbl.remove read.readers reader.id
  else
    match Hashtbl.find_opt engine.readers_of_base_nodes read.id with
    | Some table ->
        Hashtbl.remove table reader.id;
        if Hashtbl.length table = 0 then Hashtbl.remove engine.readers_of_base_nodes read.id
    | None -> ()
