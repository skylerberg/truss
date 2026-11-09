(* The code database's engine. See incremental.mli and DATABASE.md, "The
   engine".

   An engine is one state. It holds what differs from its bases, which are
   frozen engines: an input it sets, a result it computes, and a copy of
   each base result that a change of its own reached. A node knows what it
   read, in order, and what reads it.

   A change is pushed, one phase at a time. Each query has a phase, and reads
   only its own phase and earlier ones, so when a phase is brought up to
   date every earlier one is final. The results of a phase that read
   something that really changed are marked, with what reads those within
   the phase; each marked result is then brought up to date, by checking
   what it read in order and computing it only if one of those came out
   different; and only the results that came out different mark anything in
   the phases after. So a result that comes out the same stops the push
   there, and what a change costs follows what it changed.

   A clock orders changes: each change takes the next time, a node records
   when its result last changed and when it was last found current, and a
   reader is computed again when something it read changed after it was
   found current. *)

exception Cycle of string list

type subject = { path : Path.t; part : string option }

type counters = {
  marked : int;
  confirmed : int;
  computed : int;
  changed : int;
  adopted : int;
  copied : int;
  dropped : int;
}

type tally = {
  mutable marks : int;
  mutable confirmations : int;
  mutable computations : int;
  mutable changes : int;
  mutable adoptions : int;
  mutable copies : int;
  mutable drops : int;
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

type t = {
  id : int;
  bases : t list;  (** Frozen engines, each read where this one holds nothing *)
  mutable frozen : bool;
  mutable fixed : bool;  (** A frozen base whose inputs no engine over it replaces *)
  tables : (int, binding) Hashtbl.t;  (** Each input's and query's cells here, by its number *)
  own : (int, node) Hashtbl.t;
  foreign : (int, (int, node) Hashtbl.t) Hashtbl.t;
      (** What here reads a base's node, by that node's id *)
  shadows : (int, node) Hashtbl.t;  (** The copy here of a base's node, by that node's id *)
  pinned : (int, unit) Hashtbl.t;  (** Base nodes read from outside any query *)
  mutable clock : int;
  mutable frames : frame list;
  seeds : node list array;  (** By phase: readers of a result that changed, to be marked *)
  marks : node list array;  (** By phase: marked results, newest first *)
  mutable waiting : int;  (** How many seeds and marks there are *)
  mutable limbo : node list;  (** Nodes to drop, if still unread, once nothing runs *)
  logging : bool;
  mutable log : string list;
  mutable computed : node list;  (** Newest first *)
  mutable changed : node list;  (** Newest first *)
  tally : tally;
  mutable store : store option;
  unsaved : (int, node) Hashtbl.t;  (** Saved nodes made or changed since the last write *)
  mutable gone : (string * string) list;  (** Written nodes dropped since the last write *)
  mutable chain : string option;  (** The artifact last written, or opened from *)
  mutable on_whole : bool;
      (** Whether the engine's bases hold the whole state its chain starts from *)
  mutable whole : int;  (** How many nodes the chain's whole state holds *)
  mutable differences : int;  (** How many the differences after it hold *)
  mutable depth : int;  (** How many differences there are *)
  mutable activity : int;
  mutable audited : int;
}

and binding = Binding : 'table Type.Id.t * 'table -> binding

and node = {
  id : int;
  engine : t;
  phase : int;
  below : node option;  (** The base's node this one replaces *)
  mutable cell : cell;
  mutable reads : node list;  (** In the order they were first read *)
  readers : (int, node) Hashtbl.t;  (** In this node's own engine *)
  mutable marked : bool;
  mutable busy : bool;  (** Being computed, or having its reads checked *)
  mutable changed_at : int;
  mutable verified_at : int;
  mutable kept : bool;
  mutable alive : bool;
  mutable fingerprint : string option;  (** The name of its value in the store *)
  mutable identity : string option;
  mutable written : bool;  (** In the chain of artifacts *)
  mutable superseding : bool;  (** In one of the chain's differences *)
}

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

(* [Stored]: the value is in the store, under the node's fingerprint. *)
and 'value slot = Unset | Set of 'value | Stored

and ('key, 'value) query = {
  number : int;
  name : string;
  show : 'key -> string;
  phase : int;
  saved : bool;
  equal : 'value -> 'value -> bool;
  about : 'key -> subject option;
  compute : context -> 'key -> 'value;
  cells : ('key, ('key, 'value) result_cell) Hashtbl.t Type.Id.t;
}

(* An outcome of [None] is a result not computed yet, or, when the node has
   a fingerprint, one whose value is in the store and not read yet. *)
and ('key, 'value) result_cell = {
  key : 'key;
  node : node;
  mutable outcome : 'value outcome option;
}

and 'value outcome = Value of 'value | Raised of exn

and frame = {
  owner : node;
  mutable read : node list;  (** Newest first *)
  seen : (int, unit) Hashtbl.t;
  mutable cyclic : string list option;
}

and context = { engine : t; frame : frame option }

type ('key, 'value) cells = ('key, ('key, 'value) result_cell) Hashtbl.t
type ('key, 'value) input_cells = ('key, ('key, 'value) input_cell) Hashtbl.t

let engines = ref 0
let nodes_made = ref 0
let numbers = ref 0

(* Engines made while auditing, held weakly so that auditing keeps none
   alive. *)
let auditing = ref false
let remembered : t Weak.t ref = ref (Weak.create 16)
let remembered_count = ref 0

(* An audit's own engines are not remembered. *)
let within_audit = ref false

let remember engine =
  if !auditing && not !within_audit then begin
    if !remembered_count = Weak.length !remembered then begin
      let live = ref [] in
      for i = 0 to Weak.length !remembered - 1 do
        match Weak.get !remembered i with Some e -> live := e :: !live | None -> ()
      done;
      let live = List.rev !live in
      let grown = Weak.create (max 16 (2 * (List.length live + 1))) in
      List.iteri (fun i e -> Weak.set grown i (Some e)) live;
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
      (fun found base -> if List.memq base found then found else found @ [ base ])
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
      foreign = Hashtbl.create 64;
      shadows = Hashtbl.create 64;
      pinned = Hashtbl.create 16;
      clock = 1;
      frames = [];
      seeds = Array.make phases [];
      marks = Array.make phases [];
      waiting = 0;
      limbo = [];
      logging = log;
      log = [];
      computed = [];
      changed = [];
      tally =
        {
          marks = 0;
          confirmations = 0;
          computations = 0;
          changes = 0;
          adoptions = 0;
          copies = 0;
          drops = 0;
        };
      store = List.find_map (fun base -> base.store) all;
      unsaved = Hashtbl.create 256;
      gone = [];
      chain = None;
      on_whole = false;
      whole = 0;
      differences = 0;
      depth = 0;
      activity = 0;
      audited = 0;
    }
  in
  remember engine;
  engine

let is_frozen engine = engine.frozen
let bases engine = engine.bases
let context engine = { engine; frame = None }
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
    dropped = engine.tally.drops;
  }

let tick engine =
  engine.clock <- engine.clock + 1;
  engine.clock

(* Nodes *)

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

(* Whether a node's value is kept in the store: an input's, and a saved
   query's result. Every other result has a fingerprint and no bytes there,
   and is computed again where its value is needed. *)
let keeps_bytes (node : node) =
  match node.cell with Input _ -> true | Result (query, _) -> query.saved | Unfilled -> false

(* A key's bytes are the same for equal keys, which a hash of them needs. *)
let key_bytes (node : node) =
  match node.cell with
  | Input (_, cell) -> Marshal.to_string cell.input_key [ Marshal.No_sharing ]
  | Result (_, cell) -> Marshal.to_string cell.key [ Marshal.No_sharing ]
  | Unfilled -> ""

(* What names a node in every engine and every process: its input or query
   and its key. *)
let identity (node : node) =
  match node.identity with
  | Some identity -> identity
  | None ->
      let identity = Blake3.hash (name node ^ "\000" ^ key_bytes node) in
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
      kept = false;
      alive = true;
      fingerprint = None;
      identity = None;
      written = false;
      superseding = false;
    }
  in
  Hashtbl.replace engine.own node.id node;
  node

(* The cells an input or a query has in one engine. *)

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

(* A result as an engine sees it: its own, or else a base's. *)
let find_result engine (query : ('key, 'value) query) (key : 'key) =
  let look e =
    match find_table e query.number query.cells with
    | Some table -> Hashtbl.find_opt table key
    | None -> None
  in
  match look engine with Some cell -> Some cell | None -> List.find_map look engine.bases

let find_input engine (input : ('key, 'value) input) (key : 'key) =
  let look e =
    match find_table e input.input_number input.input_cells with
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

(* Edges in from readers. A base never changes, so what an engine's own
   nodes read of it is recorded in the engine. *)

let add_reader engine (read : node) (reader : node) =
  if read.engine == engine then Hashtbl.replace read.readers reader.id reader
  else
    let table =
      match Hashtbl.find_opt engine.foreign read.id with
      | Some table -> table
      | None ->
          let table = Hashtbl.create 2 in
          Hashtbl.replace engine.foreign read.id table;
          table
    in
    Hashtbl.replace table reader.id reader

let remove_reader engine (read : node) (reader : node) =
  if read.engine == engine then Hashtbl.remove read.readers reader.id
  else
    match Hashtbl.find_opt engine.foreign read.id with
    | Some table ->
        Hashtbl.remove table reader.id;
        if Hashtbl.length table = 0 then Hashtbl.remove engine.foreign read.id
    | None -> ()

(* A node as an engine sees it: its own copy, if it has made one. *)
let resolve engine (node : node) =
  if node.engine == engine then node
  else match Hashtbl.find_opt engine.shadows node.id with Some own -> own | None -> node

(* Dropping. A node nothing reads is dropped only once nothing is running:
   a query that is still running has read nodes that do not yet count it as
   a reader. A copy of a base's node stays, since the base's readers may
   read it. *)

let consider engine (node : node) =
  if node.engine == engine && node.below = None && not node.kept then
    engine.limbo <- node :: engine.limbo

let forget engine (node : node) =
  match node.cell with
  | Result (query, cell) -> (
      match find_table engine query.number query.cells with
      | Some table -> Hashtbl.remove table cell.key
      | None -> ())
  | Input (input, cell) -> (
      match find_table engine input.input_number input.input_cells with
      | Some table -> Hashtbl.remove table cell.input_key
      | None -> ())
  | Unfilled -> ()

(* A result can be dropped, and an input only while it is not set: one that
   is set holds what the database gave it. *)
let can_be_dropped (node : node) =
  match node.cell with
  | Input (_, { slot = Unset; _ }) | Result _ -> true
  | Input _ | Unfilled -> false

let rec drop engine (node : node) =
  if
    node.alive && (not node.kept) && (not node.busy) && node.below = None
    && Hashtbl.length node.readers = 0
    && can_be_dropped node
  then begin
    node.alive <- false;
    forget engine node;
    Hashtbl.remove engine.own node.id;
    Hashtbl.remove engine.unsaved node.id;
    if node.written then engine.gone <- (name node, key_bytes node) :: engine.gone;
    engine.tally.drops <- engine.tally.drops + 1;
    let reads = node.reads in
    node.reads <- [];
    List.iter
      (fun read ->
        remove_reader engine read node;
        drop_or_wait engine read)
      reads
  end

and drop_or_wait engine (node : node) =
  if engine.frames = [] then (if node.engine == engine then drop engine node)
  else consider engine node

let rec sweep engine =
  if engine.frames = [] then
    match engine.limbo with
    | [] -> ()
    | waiting ->
        engine.limbo <- [];
        List.iter (drop engine) waiting;
        sweep engine

(* Replaces a node's reads, adding it to the readers of what it reads now
   before taking it from the readers of what it no longer reads. *)
let commit_reads engine (node : node) (reads : node list) =
  List.iter (fun read -> add_reader engine read node) reads;
  let now = Hashtbl.create (List.length reads) in
  List.iter (fun (read : node) -> Hashtbl.replace now read.id ()) reads;
  let old = node.reads in
  node.reads <- reads;
  List.iter
    (fun (read : node) ->
      if not (Hashtbl.mem now read.id) then begin
        remove_reader engine read node;
        consider engine read
      end)
    old;
  List.length old <> List.length reads || List.exists2 ( != ) old reads

(* Copies a base's node into an engine, where a change may have reached it.
   The copy holds the same result and reads what the base's node read, as
   the engine sees each, and what the engine's own nodes read of the base's
   node they now read of the copy. *)
let shadow engine (base : node) =
  match Hashtbl.find_opt engine.shadows base.id with
  | Some own -> own
  | None ->
      let own =
        match base.cell with
        | Result (query, cell) ->
            let copy = make_result engine query cell.key ~below:(Some base) in
            copy.outcome <- cell.outcome;
            copy.node
        | Input (input, cell) ->
            let copy = make_input engine input cell.input_key ~below:(Some base) in
            copy.slot <- cell.slot;
            copy.input_node
        | Unfilled -> invalid_arg "Incremental: a node with no cell"
      in
      own.fingerprint <- base.fingerprint;
      own.identity <- base.identity;
      own.kept <- base.kept || Hashtbl.mem engine.pinned base.id;
      own.written <- true;
      Hashtbl.replace engine.shadows base.id own;
      engine.tally.copies <- engine.tally.copies + 1;
      let reads = List.map (resolve engine) base.reads in
      own.reads <- reads;
      List.iter (fun read -> add_reader engine read own) reads;
      (match Hashtbl.find_opt engine.foreign base.id with
      | Some readers ->
          Hashtbl.remove engine.foreign base.id;
          Hashtbl.iter
            (fun _ (reader : node) ->
              reader.reads <- List.map (fun read -> if read == base then own else read) reader.reads;
              Hashtbl.replace own.readers reader.id reader)
            readers
      | None -> ());
      own

(* What reads one of an engine's own nodes: its own readers, and, when it
   is a copy, what read the base's node in the bases, each copied into the
   engine unless it already was, since its copy is then among the own
   readers if it still reads this. [phase] narrows to one phase. *)
let readers_here engine (node : node) ~phase =
  let wanted (reader : node) = match phase with Some p -> reader.phase = p | None -> true in
  let own =
    Hashtbl.fold
      (fun _ (reader : node) found -> if wanted reader then reader :: found else found)
      node.readers []
  in
  match node.below with
  | None -> own
  | Some base ->
      let from table found =
        Hashtbl.fold
          (fun _ (reader : node) found ->
            if (not (wanted reader)) || Hashtbl.mem engine.shadows reader.id then found
            else shadow engine reader :: found)
          table found
      in
      List.fold_left
        (fun found (other : t) ->
          match Hashtbl.find_opt other.foreign base.id with
          | Some table -> from table found
          | None -> found)
        (from base.readers own) engine.bases

(* Marks a result, and what reads it within its phase, as possibly changed.
   What reads it from a later phase is left alone until it is known to have
   changed. *)
let mark ?(every_phase = false) engine (start : node) =
  let stack = Stack.create () in
  Stack.push start stack;
  while not (Stack.is_empty stack) do
    let node = Stack.pop stack in
    if node.alive && (not node.marked) && not (is_input node) then begin
      node.marked <- true;
      engine.tally.marks <- engine.tally.marks + 1;
      engine.marks.(node.phase) <- node :: engine.marks.(node.phase);
      engine.waiting <- engine.waiting + 1;
      List.iter
        (fun reader -> Stack.push reader stack)
        (readers_here engine node ~phase:(if every_phase then None else Some node.phase))
    end
  done

(* A node's result changed: what reads it is to be marked when its phase is
   reached. *)
let seed engine (node : node) =
  List.iter
    (fun (reader : node) ->
      if not reader.marked then begin
        engine.seeds.(reader.phase) <- reader :: engine.seeds.(reader.phase);
        engine.waiting <- engine.waiting + 1
      end)
    (readers_here engine node ~phase:None)

let record (context : context) (node : node) =
  match context.frame with
  | Some frame ->
      if not (Hashtbl.mem frame.seen node.id) then begin
        Hashtbl.replace frame.seen node.id ();
        frame.read <- node :: frame.read
      end
  | None ->
      let engine = context.engine in
      if not engine.frozen then
        if node.engine == engine then node.kept <- true
        else if not node.kept then Hashtbl.replace engine.pinned node.id ()

(* A cycle: every frame from the one for [node] to the newest is on it, so
   each of their results is the cycle. *)
let cycle engine (node : node) =
  let rec on_cycle found = function
    | [] -> None
    | frame :: rest ->
        let found = frame :: found in
        if frame.owner == node then Some found else on_cycle found rest
  in
  match on_cycle [] engine.frames with
  | None -> [ label node ]
  | Some frames ->
      let labels = List.map (fun frame -> label frame.owner) frames in
      List.iter (fun frame -> frame.cyclic <- Some labels) frames;
      labels

(* Values in the store *)

let unmarshal bytes = Marshal.from_string bytes 0

(* The fingerprint of an input that is not set. *)
let unset = String.make 32 '\000'

let fingerprint engine (node : node) =
  match node.fingerprint with
  | Some fingerprint -> Some fingerprint
  | None -> (
      match engine.store with
      | None -> None
      | Some store ->
          let bytes =
            match node.cell with
            | Input (_, { slot = Set value; _ }) -> Some (Marshal.to_string value [])
            | Result (_, { outcome = Some (Value value); _ }) -> (
                (* A value that holds functions has no bytes. *)
                try Some (Marshal.to_string value []) with Invalid_argument _ -> None)
            | _ -> None
          in
          Option.map
            (fun bytes ->
              let fingerprint = if keeps_bytes node then store.put bytes else Blake3.hash bytes in
              node.fingerprint <- Some fingerprint;
              fingerprint)
            bytes)

(* What a fact's key takes of a node: its fingerprint, or that it is an
   input that is not set. *)
let key_part engine (node : node) =
  match node.cell with Input (_, { slot = Unset; _ }) -> Some unset | _ -> fingerprint engine node

let input_value engine (cell : ('key, 'value) input_cell) : 'value option =
  match cell.slot with
  | Unset -> None
  | Set value -> Some value
  | Stored -> (
      match (cell.input_node.fingerprint, engine.store) with
      | Some fingerprint, Some store -> (
          match store.get fingerprint with
          | Some bytes ->
              let value = unmarshal bytes in
              cell.slot <- Set value;
              Some value
          | None -> None)
      | _ -> None)

(* The outcome in memory, reading a stored one. [None] when there is none,
   or the store no longer has it. *)
let load engine (cell : ('key, 'value) result_cell) : 'value outcome option =
  match cell.outcome with
  | Some outcome -> Some outcome
  | None when not (keeps_bytes cell.node) -> None
  | None -> (
      match (cell.node.fingerprint, engine.store) with
      | Some fingerprint, Some store -> (
          match store.get fingerprint with
          | Some bytes ->
              let outcome = Value (unmarshal bytes) in
              cell.outcome <- Some outcome;
              Some outcome
          | None -> None)
      | _ -> None)

let same_exception left right =
  match (left, right) with
  | Cycle _, Cycle _ -> true
  | _ -> ( try left = right with Invalid_argument _ -> false)

let same_outcomes (query : ('key, 'value) query) left right =
  match (left, right) with
  | Value left, Value right -> query.equal left right
  | Raised left, Raised right -> same_exception left right
  | _ -> false

(* What a result read, as a state and a fact record it: each node it read,
   in the order they were first read. A read that has no fingerprint,
   because it raised or its value holds functions, cannot be compared, so
   it is gone through, to what it read in turn. *)
let traced_reads engine (node : node) =
  let seen = Hashtbl.create 16 in
  let found = ref [] in
  let rec visit (read : node) =
    let read = resolve engine read in
    if not (Hashtbl.mem seen read.id) then begin
      Hashtbl.replace seen read.id ();
      if is_input read || fingerprint engine read <> None then found := read :: !found
      else List.iter visit read.reads
    end
  in
  List.iter visit node.reads;
  List.rev !found

(* Whether what read a node recorded the node itself, or what it read. *)
let stops (node : node) =
  is_input node || node.fingerprint <> None
  || match node.cell with Result (_, { outcome = Some (Value _); _ }) -> true | _ -> false

(* A node's reads changed, so every result that recorded its reads through
   it has other reads than it was written with, and is written again. A
   base's result is copied into the engine for that. *)
let resave engine (node : node) =
  if not (stops node) then begin
    let seen = Hashtbl.create 8 in
    let rec above (node : node) =
      List.iter
        (fun (reader : node) ->
          if not (Hashtbl.mem seen reader.id) then begin
            Hashtbl.replace seen reader.id ();
            if stops reader then Hashtbl.replace engine.unsaved reader.id reader else above reader
          end)
        (readers_here engine node ~phase:None)
    in
    above node
  end

let fact_key store (node : node) (parts : (node * string) list) =
  Blake3.hash
    (String.concat ""
       ("fact\000" :: store.version :: "\000" :: identity node
       :: List.concat_map (fun (read, part) -> [ identity read; part ]) parts))

let reads_key store (node : node) =
  Blake3.hash ("reads\000" ^ store.version ^ "\000" ^ identity node)

(* Restoring nodes from a store needs each input and query by name. *)
type restorer = {
  restore : t -> key:string -> node;  (** A node of the engine's own for the key *)
  locate : t -> key:string -> node;  (** The node for the key as the engine sees it, made if none *)
  find : t -> key:string -> node option;
}

let restorers : (string, restorer) Hashtbl.t = Hashtbl.create 64

(* Bringing results up to date *)

let phase_error (reader : node) what =
  invalid_arg
    (Printf.sprintf "Incremental: %s, of phase %d, reads %s, of a later phase" (label reader)
       reader.phase what)

let wanted (node : node) = node.kept || node.below <> None || Hashtbl.length node.readers > 0

let rec ensure engine (node : node) =
  if node.engine == engine then
    match node.cell with
    | Result (query, cell) -> ensure_result engine query cell
    | Input _ | Unfilled -> ()

and ensure_result : 'key 'value. t -> ('key, 'value) query -> ('key, 'value) result_cell -> unit =
 fun engine query cell ->
  let node = cell.node in
  if node.busy then ()
  else if node.marked then verify engine query cell
  else
    match (cell.outcome, node.fingerprint) with
    | Some _, _ | None, Some _ -> ()
    | None, None -> if not (adopt_new engine query cell) then compute engine query cell

(* Checks what a marked result read, in order, and computes it again only
   if one of those changed since it was last found current. The check stops
   at the first such read, since a later one may not be read at all once an
   earlier one gives a different answer. *)
and verify : 'key 'value. t -> ('key, 'value) query -> ('key, 'value) result_cell -> unit =
 fun engine query cell ->
  let node = cell.node in
  node.busy <- true;
  let frame = { owner = node; read = []; seen = Hashtbl.create 1; cyclic = None } in
  engine.frames <- frame :: engine.frames;
  let finish () =
    engine.frames <- List.tl engine.frames;
    node.busy <- false
  in
  let rec stale = function
    | [] -> false
    | read :: rest ->
        let read = resolve engine read in
        if read.engine != engine then stale rest
        else if read.busy then true
        else begin
          ensure engine read;
          read.changed_at > node.verified_at || stale rest
        end
  in
  let needed =
    match stale node.reads with
    | needed -> needed || frame.cyclic <> None
    | exception exception_ ->
        finish ();
        raise exception_
  in
  finish ();
  if not needed then begin
    node.marked <- false;
    node.verified_at <- engine.clock;
    engine.tally.confirmations <- engine.tally.confirmations + 1
  end
  else if not (adopt engine query cell (traced_reads engine node)) then compute engine query cell

and compute : 'key 'value. t -> ('key, 'value) query -> ('key, 'value) result_cell -> unit =
 fun engine query cell ->
  let node = cell.node in
  node.busy <- true;
  let frame = { owner = node; read = []; seen = Hashtbl.create 8; cyclic = None } in
  engine.frames <- frame :: engine.frames;
  if engine.logging then engine.log <- label node :: engine.log;
  let finish () =
    engine.frames <- List.tl engine.frames;
    node.busy <- false
  in
  let outcome =
    match query.compute { engine; frame = Some frame } cell.key with
    | value -> Value value
    | exception ((Out_of_memory | Stack_overflow) as fatal) ->
        finish ();
        raise fatal
    | exception exception_ -> Raised exception_
  in
  finish ();
  let outcome = match frame.cyclic with Some labels -> Raised (Cycle labels) | None -> outcome in
  (* A read may have been copied into the engine since it was made. *)
  let reads =
    let seen = Hashtbl.create 8 in
    List.filter_map
      (fun read ->
        let read = resolve engine read in
        if Hashtbl.mem seen read.id then None
        else begin
          Hashtbl.replace seen read.id ();
          Some read
        end)
      (List.rev frame.read)
  in
  if commit_reads engine node reads then resave engine node;
  (* A result whose old value is in the store and was never read is
     compared by fingerprint, without reading the old value. *)
  let first = cell.outcome = None && node.fingerprint = None in
  let changed =
    match (cell.outcome, node.fingerprint) with
    | Some old, _ ->
        let changed = not (same_outcomes query old outcome) in
        if changed then begin
          cell.outcome <- Some outcome;
          node.fingerprint <- None
        end;
        changed
    | None, None ->
        cell.outcome <- Some outcome;
        true
    | None, Some old -> (
        cell.outcome <- Some outcome;
        node.fingerprint <- None;
        match fingerprint engine node with Some now -> now <> old | None -> true)
  in
  if changed then begin
    node.changed_at <- tick engine;
    engine.changed <- node :: engine.changed;
    engine.tally.changes <- engine.tally.changes + 1;
    (* What read a result while it was first being computed is on a cycle
       with it, and has the cycle as its result, as this one has. *)
    if not first then seed engine node
  end;
  node.verified_at <- engine.clock;
  node.marked <- false;
  engine.computed <- node :: engine.computed;
  engine.tally.computations <- engine.tally.computations + 1;
  engine.activity <- engine.activity + 1;
  Hashtbl.replace engine.unsaved node.id node

(* Looks for a result as a fact, under the key of [candidates], which are
   what it read before, with the fingerprints they have now. A fact found
   was computed from reads with exactly these fingerprints, and a query is a
   function of what it reads, so computing it now would read the same and
   give the same. *)
and adopt :
    'key 'value. t -> ('key, 'value) query -> ('key, 'value) result_cell -> node list -> bool =
 fun engine query cell candidates ->
  let node = cell.node in
  match engine.store with
  | Some store when query.saved && candidates <> [] -> (
      let was_marked = node.marked in
      let held () = cell.outcome <> None || node.fingerprint <> None in
      let had = held () in
      let rec parts found = function
        | [] -> Some (List.rev found)
        | read :: rest ->
            let read = resolve engine read in
            if read.busy || read.phase > node.phase then None
            else begin
              ensure engine read;
              match key_part engine read with
              | Some part -> parts ((read, part) :: found) rest
              | None -> None
            end
      in
      match parts [] candidates with
      | None -> false
      | Some parts -> (
          if
            (* Bringing the candidates up to date may have brought this result
             up to date too, where they read it. *)
            (was_marked && not node.marked) || ((not had) && held ())
          then true
          else
            match store.find ~kind:"fact" ~key:(fact_key store node parts) with
            | None -> false
            | Some found ->
                let unchanged = had && fingerprint engine node = Some found in
                if commit_reads engine node (List.map fst parts) then resave engine node;
                if not unchanged then begin
                  cell.outcome <- None;
                  node.fingerprint <- Some found;
                  node.changed_at <- tick engine;
                  engine.changed <- node :: engine.changed;
                  engine.tally.changes <- engine.tally.changes + 1;
                  seed engine node
                end;
                node.verified_at <- engine.clock;
                node.marked <- false;
                engine.tally.adoptions <- engine.tally.adoptions + 1;
                engine.activity <- engine.activity + 1;
                Hashtbl.replace engine.unsaved node.id node;
                true))
  | _ -> false

(* A result the engine has never held: what a result of its query and key
   read, wherever one was first computed, says what to look for. *)
and adopt_new : 'key 'value. t -> ('key, 'value) query -> ('key, 'value) result_cell -> bool =
 fun engine query cell ->
  match engine.store with
  | Some store when query.saved -> (
      match store.find ~kind:"reads" ~key:(reads_key store cell.node) with
      | None -> false
      | Some bytes ->
          let named : (string * string) list = unmarshal bytes in
          let located =
            List.map
              (fun (name, key) ->
                match Hashtbl.find_opt restorers name with
                | Some restorer -> ( try Some (restorer.locate engine ~key) with _ -> None)
                | None -> None)
              named
          in
          let candidates = List.filter_map Fun.id located in
          let adopted = List.for_all Option.is_some located && adopt engine query cell candidates in
          (* A node made only to look is dropped if nothing came to read it. *)
          if not adopted then List.iter (consider engine) candidates;
          adopted)
  | _ -> false

(* Brings every result the engine holds up to date: the lowest phase with
   anything to mark or to check, then the next, until none has. *)
let lowest engine =
  let rec find phase =
    if phase >= phases then None
    else if engine.seeds.(phase) <> [] || engine.marks.(phase) <> [] then Some phase
    else find (phase + 1)
  in
  find 0

let rec settle engine =
  if engine.waiting > 0 then
    match lowest engine with
    | None -> engine.waiting <- 0
    | Some phase ->
        let seeds = engine.seeds.(phase) in
        engine.seeds.(phase) <- [];
        engine.waiting <- engine.waiting - List.length seeds;
        List.iter (mark engine) seeds;
        (* Newest first: a result marked later reads one marked earlier, and
           checking it may show that the earlier one is no longer read. *)
        let marked = engine.marks.(phase) in
        engine.marks.(phase) <- [];
        engine.waiting <- engine.waiting - List.length marked;
        List.iter
          (fun (node : node) ->
            if node.alive && node.marked && wanted node then ensure engine node;
            sweep engine)
          marked;
        sweep engine;
        settle engine

let check_can_change engine =
  if engine.frozen then invalid_arg "Incremental: a frozen engine cannot change";
  if engine.frames <> [] then invalid_arg "Incremental: an input changed while a query was running"

(* Inputs *)

let input ~name ~show ?(equal = ( = )) ?(about = fun _ -> None) () =
  incr numbers;
  let input =
    {
      input_number = !numbers;
      input_name = name;
      input_show = show;
      input_equal = equal;
      input_about = about;
      input_cells = Type.Id.make ();
    }
  in
  let own engine key =
    match Hashtbl.find_opt (input_cells engine input) key with
    | Some cell -> cell
    | None ->
        let below = Option.map (fun cell -> cell.input_node) (find_input engine input key) in
        let cell = make_input engine input key ~below in
        Option.iter
          (fun (base : node) -> Hashtbl.replace engine.shadows base.id cell.input_node)
          below;
        cell
  in
  Hashtbl.replace restorers name
    {
      restore = (fun engine ~key -> (own engine (unmarshal key)).input_node);
      locate =
        (fun engine ~key ->
          let key = unmarshal key in
          match find_input engine input key with
          | Some cell -> cell.input_node
          | None ->
              let cell = make_input engine input key ~below:None in
              Hashtbl.replace engine.unsaved cell.input_node.id cell.input_node;
              cell.input_node);
      find =
        (fun engine ~key ->
          Option.map (fun cell -> cell.input_node) (find_input engine input (unmarshal key)));
    };
  input

let read (context : context) (input : ('key, 'value) input) (key : 'key) : 'value option =
  let engine = context.engine in
  (match context.frame with None when not engine.frozen -> settle engine | _ -> ());
  match find_input engine input key with
  | Some cell ->
      record context cell.input_node;
      input_value engine cell
  | None ->
      if engine.frozen then None
      else begin
        (* A read that found nothing is read too, and is part of the state. *)
        let cell = make_input engine input key ~below:None in
        Hashtbl.replace engine.unsaved cell.input_node.id cell.input_node;
        record context cell.input_node;
        None
      end

let change engine (cell : ('key, 'value) input_cell) slot =
  let node = cell.input_node in
  cell.slot <- slot;
  node.fingerprint <- None;
  node.changed_at <- tick engine;
  engine.activity <- engine.activity + 1;
  Hashtbl.replace engine.unsaved node.id node;
  seed engine node

(* The engine's own cell for an input, copying a base's if it has one. *)
let own_input engine (input : ('key, 'value) input) key =
  match find_input engine input key with
  | Some cell when cell.input_node.engine == engine -> cell
  | Some base ->
      ignore (shadow engine base.input_node);
      Hashtbl.find (input_cells engine input) key
  | None -> make_input engine input key ~below:None

let set engine (input : ('key, 'value) input) key value =
  check_can_change engine;
  let same =
    match find_input engine input key with
    | Some cell -> (
        match input_value engine cell with Some old -> input.input_equal old value | None -> false)
    | None -> false
  in
  if not same then change engine (own_input engine input key) (Set value)

let remove engine (input : ('key, 'value) input) key =
  check_can_change engine;
  match find_input engine input key with
  | Some { slot = Set _ | Stored; _ } -> change engine (own_input engine input key) Unset
  | Some { slot = Unset; _ } | None -> ()

(* Queries *)

let query ~name ~show ~phase ?(saved = false) ?(equal = ( = )) ?(about = fun _ -> None) compute =
  if phase < 1 || phase >= phases then invalid_arg "Incremental.query: no such phase";
  incr numbers;
  let query =
    { number = !numbers; name; show; phase; saved; equal; about; compute; cells = Type.Id.make () }
  in
  Hashtbl.replace restorers name
    {
      restore =
        (fun engine ~key ->
          let key = unmarshal key in
          match Hashtbl.find_opt (result_cells engine query) key with
          | Some cell -> cell.node
          | None ->
              let below = Option.map (fun cell -> cell.node) (find_result engine query key) in
              let cell = make_result engine query key ~below in
              Option.iter
                (fun (base : node) -> Hashtbl.replace engine.shadows base.id cell.node)
                below;
              cell.node);
      locate =
        (fun engine ~key ->
          let key = unmarshal key in
          match find_result engine query key with
          | Some cell -> cell.node
          | None -> (make_result engine query key ~below:None).node);
      find =
        (fun engine ~key ->
          Option.map (fun cell -> cell.node) (find_result engine query (unmarshal key)));
    };
  query

(* The value of a result that is up to date. A stored value the store no
   longer has is computed again, in the engine itself. *)
let rec value : 'key 'value. t -> ('key, 'value) query -> ('key, 'value) result_cell -> 'value =
 fun engine query cell ->
  match load engine cell with
  | Some (Value value) -> value
  | Some (Raised exception_) -> raise exception_
  | None ->
      let node = cell.node in
      if node.engine == engine then begin
        if node.busy then invalid_arg ("Incremental: no result for " ^ label node);
        let before = node.changed_at in
        compute engine query cell;
        (* A lost value that comes back different has readers that were
           found current against the old one. *)
        if node.changed_at <> before then
          List.iter (mark ~every_phase:true engine) (readers_here engine node ~phase:None);
        match cell.outcome with
        | Some (Value value) -> value
        | Some (Raised exception_) -> raise exception_
        | None -> invalid_arg ("Incremental: no result for " ^ label node)
      end
      else begin
        ignore (shadow engine node);
        value engine query (Hashtbl.find (result_cells engine query) cell.key)
      end

let demand (context : context) (query : ('key, 'value) query) (key : 'key) : 'value =
  let engine = context.engine in
  (match context.frame with
  | Some frame ->
      if query.phase > frame.owner.phase then
        phase_error frame.owner (Printf.sprintf "%s(%s)" query.name (query.show key))
  | None -> if not engine.frozen then settle engine);
  let cell =
    match find_result engine query key with
    | Some cell -> cell
    | None ->
        if engine.frozen then invalid_arg "Incremental: a frozen engine cannot compute"
        else make_result engine query key ~below:None
  in
  let node = cell.node in
  if node.engine == engine && not engine.frozen then begin
    if node.busy then begin
      let labels = cycle engine node in
      record context node;
      raise (Cycle labels)
    end;
    ensure_result engine query cell
  end;
  record context node;
  let result = match value engine query cell with value -> Ok value | exception e -> Error e in
  (match (context.frame, result) with
  | None, _ -> sweep engine
  | Some frame, Error (Cycle labels) ->
      (* A cycle is an error wherever it is met: what reads a result that
         is a cycle has the cycle as its own, whether or not it catches it,
         so that its result does not depend on which query met the cycle
         first. *)
      if frame.cyclic = None then frame.cyclic <- Some labels
  | Some _, _ -> ());
  match result with Ok value -> value | Error exception_ -> raise exception_

(* Engines *)

type change = { computed : node list; changed : node list }

let stabilize engine =
  check_can_change engine;
  sweep engine;
  settle engine;
  let change = { computed = List.rev engine.computed; changed = List.rev engine.changed } in
  engine.computed <- [];
  engine.changed <- [];
  change

let freeze ?(fixed = false) engine =
  if not engine.frozen then begin
    check_can_change engine;
    sweep engine;
    settle engine;
    if Hashtbl.length engine.shadows > 0 then
      invalid_arg "Incremental.freeze: an engine that replaces results of its bases";
    engine.frozen <- true;
    engine.fixed <- fixed
  end

let release engine (query : ('key, 'value) query) key =
  match Hashtbl.find_opt (result_cells engine query) key with
  | Some cell ->
      cell.node.kept <- false;
      drop_or_wait engine cell.node;
      sweep engine
  | None -> ()

let executed engine = List.rev engine.log
let clear_log engine = engine.log <- []

(* The graph *)

let by_id nodes = List.sort (fun (a : node) (b : node) -> compare a.id b.id) nodes
let differing engine = by_id (Hashtbl.fold (fun _ node found -> node :: found) engine.own [])
let count engine = Hashtbl.length engine.own

let unshared engine other =
  let found = Hashtbl.fold (fun _ node found -> node :: found) engine.own [] in
  by_id
    (List.fold_left
       (fun found (base : t) ->
         if base.fixed || List.memq base other.bases then found
         else
           Hashtbl.fold
             (fun _ (node : node) found ->
               if Hashtbl.mem engine.shadows node.id then found else node :: found)
             base.own found)
       found engine.bases)

(* The state's nodes, apart from its fixed bases': the engine's own, and
   those of an earlier state it has not replaced. *)
let nodes engine =
  let found = Hashtbl.fold (fun _ node found -> node :: found) engine.own [] in
  by_id
    (List.fold_left
       (fun found (base : t) ->
         if base.fixed then found
         else
           Hashtbl.fold
             (fun _ (node : node) found ->
               if Hashtbl.mem engine.shadows node.id then found else node :: found)
             base.own found)
       found engine.bases)

let reads engine (node : node) = List.map (resolve engine) node.reads

(* What reads a node, without copying anything: a base's reader that the
   engine has not copied reads the engine's copy as it read the base's
   node. *)
let readers engine (node : node) =
  let below = if node.engine == engine then node.below else Some node in
  let own =
    if node.engine == engine then
      Hashtbl.fold (fun _ reader found -> reader :: found) node.readers []
    else
      match Hashtbl.find_opt engine.foreign node.id with
      | Some table -> Hashtbl.fold (fun _ reader found -> reader :: found) table []
      | None -> []
  in
  let found =
    match below with
    | None -> own
    | Some base ->
        let from table found =
          Hashtbl.fold
            (fun _ (reader : node) found ->
              if Hashtbl.mem engine.shadows reader.id then found else reader :: found)
            table found
        in
        List.fold_left
          (fun found (other : t) ->
            match Hashtbl.find_opt other.foreign base.id with
            | Some table -> from table found
            | None -> found)
          (if base.engine == engine then own else from base.readers own)
          engine.bases
  in
  by_id found

let counterpart (node : node) other =
  match node.cell with
  | Input (input, cell) ->
      Option.map (fun cell -> cell.input_node) (find_input other input cell.input_key)
  | Result (query, cell) -> Option.map (fun cell -> cell.node) (find_result other query cell.key)
  | Unfilled -> None

let current_in (node : node) other =
  match node.cell with
  | Input (input, cell) ->
      Option.map (fun cell -> cell.input_node) (find_input other input cell.input_key)
  | Result (query, cell) ->
      (try ignore (demand (context other) query cell.key) with _ -> ());
      Option.map (fun cell -> cell.node) (find_result other query cell.key)
  | Unfilled -> None

let same_outcome engine (left : node) other (right : node) =
  match left.cell with
  | Input (input, mine) -> (
      match find_input other input mine.input_key with
      | Some theirs when theirs.input_node == right -> (
          match (input_value engine mine, input_value other theirs) with
          | Some mine, Some theirs -> input.input_equal mine theirs
          | None, None -> true
          | _ -> false)
      | _ -> false)
  | Result (query, mine) -> (
      match find_result other query mine.key with
      | Some theirs when theirs.node == right -> (
          match (left.fingerprint, right.fingerprint) with
          | Some mine, Some theirs when mine = theirs -> true
          | _ -> (
              match (load engine mine, load other theirs) with
              | Some mine, Some theirs -> same_outcomes query mine theirs
              | _ -> false))
      | _ -> false)
  | Unfilled -> false

(* Facts and states in a store *)

let require_store engine =
  match engine.store with
  | Some store -> store
  | None -> invalid_arg "Incremental: no store is attached"

let record_fact engine store (node : node) =
  match node.cell with
  | Result (query, _) when query.saved -> (
      match fingerprint engine node with
      | None -> ()
      | Some value -> (
          let reads = traced_reads engine node in
          let parts =
            List.fold_right
              (fun read found ->
                match (found, key_part engine read) with
                | Some found, Some part -> Some ((read, part) :: found)
                | _ -> None)
              reads (Some [])
          in
          match parts with
          | None | Some [] -> ()
          | Some parts ->
              store.add ~kind:"fact" ~key:(fact_key store node parts) value;
              let key = reads_key store node in
              if store.find ~kind:"reads" ~key = None then
                store.add ~kind:"reads" ~key
                  (Marshal.to_string
                     (List.map (fun (read, _) -> (name read, key_bytes read)) parts)
                     [])))
  | _ -> ()

let unsaved_nodes engine =
  by_id
    (Hashtbl.fold
       (fun _ (node : node) found -> if node.alive then node :: found else found)
       engine.unsaved [])

let record engine =
  match engine.store with
  | None -> ()
  | Some store -> List.iter (record_fact engine store) (unsaved_nodes engine)

(* An artifact: a state, or what changed in one since an earlier artifact.
   Each node is named by its input or query and its key, and what it read
   by places in the artifact's table of such names. *)
type saved_node = {
  saved_name : string;
  saved_key : string;
  saved_value : string option;  (** A fingerprint; [None] for an input that is not set *)
  saved_reads : int list;
  saved_kept : bool;
}

type artifact = {
  base : string option;
  saved : saved_node list;
  table : (string * string) array;
  dropped : (string * string) list;
  whole_size : int;
  difference_size : int;
  difference_count : int;
}

(* The same read in the same order names the same nodes. *)
let same_reads engine (left : node) (right : node) =
  let ids node = List.map (fun (read : node) -> identity read) (traced_reads engine node) in
  ids left = ids right

let write ?(full = false) engine =
  let store = require_store engine in
  check_can_change engine;
  sweep engine;
  settle engine;
  let full = full || engine.chain = None in
  let kept (node : node) = node.kept || Hashtbl.mem engine.pinned node.id in
  let candidates =
    if full then begin
      (* What the kept results and the set inputs reach, apart from the
         fixed bases. *)
      let reached = Hashtbl.create 1024 in
      let rec reach (node : node) =
        if (not node.engine.fixed) && not (Hashtbl.mem reached node.id) then begin
          Hashtbl.replace reached node.id node;
          List.iter (fun read -> reach (resolve engine read)) node.reads
        end
      in
      List.iter
        (fun (node : node) ->
          let set =
            match node.cell with Input (_, { slot = Set _ | Stored; _ }) -> true | _ -> false
          in
          if kept node || set then reach node)
        (nodes engine);
      by_id (Hashtbl.fold (fun _ node found -> node :: found) reached [])
    end
    else unsaved_nodes engine
  in
  (* A node that is written must find what it read when the state is
     opened, so a node of the engine's own that the chain does not hold yet
     is written with the first node that read it. *)
  let scheduled = Hashtbl.create 256 in
  List.iter (fun (node : node) -> Hashtbl.replace scheduled node.id ()) candidates;
  let more = Queue.create () in
  let places = Hashtbl.create 256 in
  let table = ref [] in
  let place (read : node) =
    if read.engine == engine && (not read.written) && not (Hashtbl.mem scheduled read.id) then begin
      Hashtbl.replace scheduled read.id ();
      Queue.add read more
    end;
    match Hashtbl.find_opt places read.id with
    | Some place -> place
    | None ->
        let place = Hashtbl.length places in
        Hashtbl.replace places read.id place;
        table := (name read, key_bytes read) :: !table;
        place
  in
  let written (node : node) saved_value saved_reads =
    node.written <- true;
    node.superseding <- not full;
    Some
      {
        saved_name = name node;
        saved_key = key_bytes node;
        saved_value;
        saved_reads;
        saved_kept = kept node;
      }
  in
  let save (node : node) =
    if Hashtbl.mem engine.unsaved node.id then record_fact engine store node;
    (* A copy that came out as the base's node, reading the same, is the
           base's node, and is not written, unless an earlier difference
           holds another result for it, which this one takes the place of. *)
    let as_base = (not full) && engine.on_whole && not node.superseding in
    let as_below () =
      as_base
      &&
      match node.below with
      | Some base ->
          base.fingerprint = node.fingerprint
          && base.kept = kept node
          && same_reads engine node base
      | None -> false
    in
    match node.cell with
    | Input (_, { slot = Unset; _ }) -> (
        match node.below with
        | Some { cell = Input (_, { slot = Unset; _ }); _ } when as_base -> None
        | _ -> written node None [])
    | Input _ -> (
        match fingerprint engine node with
        | Some value when not (as_below ()) -> written node (Some value) []
        | _ -> None)
    | Result _ -> (
        match fingerprint engine node with
        | Some value ->
            if as_below () then None
            else written node (Some value) (List.map place (traced_reads engine node))
        | None ->
            (* A result with no fingerprint takes the place of an earlier
                   one the chain holds. *)
            if node.written && not full then written node None [] else None)
    | Unfilled -> None
  in
  let first = List.filter_map save candidates in
  let rec rest found =
    match Queue.take_opt more with
    | Some node -> rest (match save node with Some saved -> saved :: found | None -> found)
    | None -> List.rev found
  in
  let saved = first @ rest [] in
  let count = List.length saved in
  let artifact =
    {
      base = (if full then None else engine.chain);
      saved;
      table = Array.of_list (List.rev !table);
      dropped = (if full then [] else List.rev engine.gone);
      whole_size = (if full then count else engine.whole);
      difference_size = (if full then 0 else engine.differences + count);
      difference_count = (if full then 0 else engine.depth + 1);
    }
  in
  let name = store.put (Marshal.to_string artifact []) in
  if full then engine.on_whole <- false;
  engine.chain <- Some name;
  engine.whole <- artifact.whole_size;
  engine.differences <- artifact.difference_size;
  engine.depth <- artifact.difference_count;
  Hashtbl.reset engine.unsaved;
  engine.gone <- [];
  name

type debt = { whole : int; differences : int; depth : int }

let debt (engine : t) =
  { whole = engine.whole; differences = engine.differences; depth = engine.depth }

let artifact (engine : t) = engine.chain

let unwritten (engine : t) =
  engine.chain = None || Hashtbl.length engine.unsaved > 0 || engine.gone <> []

(* The artifacts from the whole state a chain starts with to its last. *)
let chain_of store name =
  let rec back name found =
    match store.get name with
    | None -> None
    | Some bytes -> (
        let artifact : artifact = unmarshal bytes in
        let found = (name, artifact) :: found in
        match artifact.base with None -> Some found | Some base -> back base found)
  in
  back name []

let values_in store name =
  match chain_of store name with
  | None -> []
  | Some chain ->
      List.concat_map
        (fun (name, artifact) ->
          name :: List.filter_map (fun (node : saved_node) -> node.saved_value) artifact.saved)
        chain

(* Fills an engine with artifacts' nodes, each the last of its name and key,
   apart from those dropped after. A node of a query this program does not
   declare is left out, and so is one that read a node that cannot be
   found, with everything that read it, since its result could not be
   checked. *)
let fill engine (artifacts : artifact list) =
  let last : (string * string, saved_node * artifact) Hashtbl.t = Hashtbl.create 1024 in
  let order = ref [] in
  let gone = Hashtbl.create 16 in
  List.iter
    (fun (artifact : artifact) ->
      List.iter
        (fun key ->
          Hashtbl.remove last key;
          Hashtbl.replace gone key ())
        artifact.dropped;
      List.iter
        (fun (node : saved_node) ->
          let key = (node.saved_name, node.saved_key) in
          if not (Hashtbl.mem last key) then order := key :: !order;
          Hashtbl.remove gone key;
          Hashtbl.replace last key (node, artifact))
        artifact.saved)
    artifacts;
  (* A node that was dropped is not in the state. Where a base holds it, the
     engine holds its place with nothing in it, so that it is computed if it
     is asked for, and the base's result, which is of an earlier state, is
     never read. *)
  Hashtbl.iter
    (fun (name, key) () ->
      match Hashtbl.find_opt restorers name with
      | Some restorer -> (
          match restorer.find engine ~key with
          | Some (found : node) when found.engine != engine -> (
              match restorer.restore engine ~key with
              | node ->
                  node.written <- true;
                  node.superseding <- true;
                  node.kept <- false
              | exception _ -> ())
          | _ | (exception _) -> ())
      | None -> ())
    gone;
  let made =
    List.filter_map
      (fun key ->
        match Hashtbl.find_opt last key with
        | None -> None
        | Some (saved, artifact) -> (
            match Hashtbl.find_opt restorers saved.saved_name with
            | None -> None
            | Some restorer -> (
                match restorer.restore engine ~key:saved.saved_key with
                | exception _ -> None
                | node ->
                    node.fingerprint <- saved.saved_value;
                    node.kept <- saved.saved_kept;
                    node.written <- true;
                    node.superseding <- true;
                    (match node.cell with
                    | Input (_, cell) ->
                        cell.slot <- (if saved.saved_value = None then Unset else Stored)
                    | Result (_, cell) -> cell.outcome <- None
                    | Unfilled -> ());
                    Some (node, saved, artifact))))
      (List.rev !order)
  in
  let find (artifact : artifact) place =
    let name, key = artifact.table.(place) in
    match Hashtbl.find_opt restorers name with
    | Some restorer -> ( try restorer.find engine ~key with _ -> None)
    | None -> None
  in
  let broken = Hashtbl.create 8 in
  List.iter
    (fun ((node : node), saved, artifact) ->
      let found = List.map (find artifact) saved.saved_reads in
      if List.exists Option.is_none found then Hashtbl.replace broken node.id node
      else begin
        let reads = List.filter_map Fun.id found in
        node.reads <- reads;
        List.iter (fun read -> add_reader engine read node) reads
      end)
    made;
  (* What cannot be checked is left out, with what reads it. One that a base
     also holds keeps its place, with nothing in it, so that the base's
     result, which is of an earlier state, is not read in its stead. *)
  let emptied = Hashtbl.create 8 in
  let rec remove (node : node) =
    if node.alive && not (Hashtbl.mem emptied node.id) then begin
      Hashtbl.replace emptied node.id ();
      let readers = Hashtbl.fold (fun _ reader found -> reader :: found) node.readers [] in
      List.iter (fun read -> remove_reader engine read node) node.reads;
      node.reads <- [];
      node.fingerprint <- None;
      (match node.cell with
      | Input (_, cell) -> cell.slot <- Unset
      | Result (_, cell) -> cell.outcome <- None
      | Unfilled -> ());
      if node.below = None then begin
        node.alive <- false;
        forget engine node;
        Hashtbl.remove engine.own node.id
      end;
      List.iter remove readers
    end
  in
  Hashtbl.iter (fun _ node -> remove node) broken

(* Frozen bases, shared by every engine opened from the same whole state
   over the same bases, and held weakly, so that one no engine uses is
   freed. *)
let shared_bases : (string, t Weak.t) Hashtbl.t = Hashtbl.create 8
let forget_bases () = Hashtbl.reset shared_bases

let frozen_from (store : store) ~bases ~fixed ~name (artifacts : artifact list) =
  let key =
    String.concat ":"
      (store.id :: name :: string_of_bool fixed
      :: List.map (fun (base : t) -> string_of_int base.id) bases)
  in
  let cached =
    match Hashtbl.find_opt shared_bases key with Some weak -> Weak.get weak 0 | None -> None
  in
  match cached with
  | Some engine -> engine
  | None ->
      let engine = create ~bases () in
      attach engine store;
      fill engine artifacts;
      engine.frozen <- true;
      engine.fixed <- fixed;
      let dead =
        Hashtbl.fold
          (fun key weak found -> if Weak.check weak 0 then found else key :: found)
          shared_bases []
      in
      List.iter (Hashtbl.remove shared_bases) dead;
      let weak = Weak.create 1 in
      Weak.set weak 0 (Some engine);
      Hashtbl.replace shared_bases key weak;
      engine

let frozen_of store ~bases ~fixed name =
  match chain_of store name with
  | None -> None
  | Some chain -> Some (frozen_from store ~bases ~fixed ~name (List.map snd chain))

let open_ ?log store ~bases name =
  match chain_of store name with
  | None | Some [] -> None
  | Some ((whole_name, whole) :: differences) ->
      let base = frozen_from store ~bases ~fixed:false ~name:whole_name [ whole ] in
      let engine = create ?log ~bases:(base :: bases) () in
      attach engine store;
      fill engine (List.map snd differences);
      let last = match List.rev differences with (_, last) :: _ -> last | [] -> whole in
      engine.chain <- Some name;
      engine.on_whole <- true;
      engine.whole <- last.whole_size;
      engine.differences <- last.difference_size;
      engine.depth <- last.difference_count;
      Some engine

(* Checking the engine *)

let describe_outcome (outcome : 'value outcome option) =
  match outcome with
  | None -> "nothing"
  | Some (Value _) -> "a value"
  | Some (Raised exception_) -> "raising " ^ Printexc.to_string exception_

let audit ?(flat = false) engine =
  if engine.frozen then []
  else begin
    check_can_change engine;
    sweep engine;
    settle engine;
    within_audit := true;
    let fresh =
      Fun.protect
        ~finally:(fun () -> within_audit := false)
        (fun () -> create ~bases:(if flat then [] else engine.bases) ())
    in
    (* The new engine reads stored values, and finds no facts, since a fact
       this engine recorded would only be its own result again. *)
    fresh.store <-
      Option.map
        (fun store ->
          {
            store with
            put = Blake3.hash;
            find = (fun ~kind:_ ~key:_ -> None);
            add = (fun ~kind:_ ~key:_ _ -> ());
          })
        engine.store;
    let replay (node : node) =
      match node.cell with
      | Input (input, cell) -> (
          match input_value engine cell with
          | Some value -> set fresh input cell.input_key value
          | None -> remove fresh input cell.input_key)
      | Result _ | Unfilled -> ()
    in
    if flat then
      List.iter
        (fun (base : t) ->
          Hashtbl.iter
            (fun _ (node : node) -> if not (Hashtbl.mem engine.shadows node.id) then replay node)
            base.own)
        (List.rev engine.bases);
    let own = differing engine in
    List.iter replay own;
    let problems =
      List.filter_map
        (fun (node : node) ->
          match node.cell with
          | Result (query, cell) when node.alive && not node.marked -> (
              match load engine cell with
              | None -> None
              | Some mine ->
                  let theirs =
                    match demand (context fresh) query cell.key with
                    | value -> Value value
                    | exception exception_ -> Raised exception_
                  in
                  if same_outcomes query mine theirs then None
                  else
                    Some
                      (Printf.sprintf "%s holds %s, and a fresh engine gives %s" (label node)
                         (describe_outcome (Some mine)) (describe_outcome (Some theirs))))
          | _ -> None)
        own
    in
    if engine.audited <> max_int then engine.audited <- engine.activity;
    problems
  end

let skip_audit engine = engine.audited <- max_int

let audit_all () =
  let found = ref [] in
  let table = !remembered in
  for i = 0 to Weak.length table - 1 do
    match Weak.get table i with
    | Some engine
      when (not engine.frozen) && engine.audited <> max_int && engine.activity <> engine.audited
           && engine.frames = [] ->
        found := audit engine @ !found
    | _ -> ()
  done;
  !found
