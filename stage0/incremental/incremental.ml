(* The code database's engine. See incremental.mli and DATABASE.md,
   "Pushing changes".

   Every node knows what it read, in order, and what reads it. Setting an
   input marks everything that can reach it, through the edges in from
   readers, as possibly changed: only flags are set, so marking costs the
   nodes a change can affect and nothing more. A marked node is brought up
   to date when it is needed, by bringing what it read up to date in order
   and computing it again only if one of those came out different since it
   was last computed. A result that comes out the same leaves its readers
   alone, which is early cutoff.

   Stamps order changes: each input change takes the next stamp, a node
   records the stamp at which its result last changed and the stamp at
   which it was last confirmed current, and a reader is computed again when
   something it read changed after it was confirmed. *)

exception Cycle of string list

type subject = { path : Path.t; part : string option }

type t = {
  id : int;
  shared : t option;
  is_frozen_layer : bool;
  mutable stamp : int;
  mutable frames : frame list;
  all : (int, node) Hashtbl.t;
  logging : bool;
  mutable log : string list;
  mutable computed : node list;  (** Newest first *)
  mutable changed : node list;  (** Newest first *)
  dirty_kept : (int, node) Hashtbl.t;
  unsaved : (int, node) Hashtbl.t;  (** Saved nodes made or changed since the last save *)
  mutable dropped : int list;  (** Journal ids *)
  mutable next_journal_id : int;
  mutable put : string -> string;
  mutable get : string -> string option;
}

and node = {
  id : int;
  name : string;
  label : string;
  mutable engine : t;
  mutable reads : node list;  (** In the order they were first read *)
  readers : (int, node) Hashtbl.t;
  mutable height : int;
  mutable dirty : bool;
  mutable busy : bool;  (** Being computed, or having its reads checked *)
  mutable changed_at : int;
  mutable verified_at : int;
  mutable kept : bool;
  mutable alive : bool;
  mutable was_saved : bool;
  mutable journal_id : int;  (** 0 until the node is first saved *)
  mutable read_once : bool;
  is_input : bool;
  saved : bool;
  mutable ops : ops;
}

and ops = {
  ensure : unit -> unit;
  forget : unit -> unit;
  subject : unit -> subject option;
  key_bytes : unit -> string;
  value_hash : unit -> string option;
  counterpart : t -> node option;
  same : node -> bool;
  move_to : t -> unit;
  copy : t -> node;  (** The same node, with its result, made in another engine *)
  current_in : t -> node option;  (** The same node in another engine, brought up to date *)
}

and frame = {
  owner : node;
  mutable read : node list;  (** Newest first *)
  seen : (int, unit) Hashtbl.t;
  mutable cyclic : string list option;
}

type context = { engine : t; frame : frame option }

let engines = ref 0
let nodes_made = ref 0

let make_engine ~logging ~shared ~is_frozen_layer =
  incr engines;
  {
    id = !engines;
    shared;
    is_frozen_layer;
    stamp = 1;
    frames = [];
    all = Hashtbl.create 1024;
    logging;
    log = [];
    computed = [];
    changed = [];
    dirty_kept = Hashtbl.create 64;
    unsaved = Hashtbl.create 1024;
    dropped = [];
    next_journal_id = 1;
    put = (fun _ -> invalid_arg "Incremental: no store to put values in");
    get = (fun _ -> None);
  }

let create ?(log = false) ?shared () =
  (match shared with
  | Some layer when not layer.is_frozen_layer ->
      invalid_arg "Incremental.create: not a frozen layer"
  | _ -> ());
  make_engine ~logging:log ~shared ~is_frozen_layer:false

let frozen_layer ?(log = false) () = make_engine ~logging:log ~shared:None ~is_frozen_layer:true
let context engine = { engine; frame = None }
let is_frozen (node : node) = node.engine.is_frozen_layer

let no_ops =
  {
    ensure = ignore;
    forget = ignore;
    subject = (fun () -> None);
    key_bytes = (fun () -> "");
    value_hash = (fun () -> None);
    counterpart = (fun _ -> None);
    same = (fun _ -> false);
    move_to = ignore;
    copy = (fun _ -> invalid_arg "Incremental: a node that cannot be copied");
    current_in = (fun _ -> None);
  }

let new_node (engine : t) ~name ~label ~is_input ~saved =
  incr nodes_made;
  let node =
    {
      id = !nodes_made;
      name;
      label;
      engine;
      reads = [];
      readers = Hashtbl.create 1;
      height = 0;
      dirty = false;
      busy = false;
      changed_at = 0;
      verified_at = 0;
      kept = false;
      alive = true;
      was_saved = false;
      journal_id = 0;
      read_once = false;
      is_input;
      saved;
      ops = no_ops;
    }
  in
  Hashtbl.replace engine.all node.id node;
  node

(* The table an input or query keeps for one engine. *)
let table tables engine =
  match Hashtbl.find_opt tables engine.id with
  | Some table -> table
  | None ->
      let table = Hashtbl.create 64 in
      Hashtbl.replace tables engine.id table;
      table

(* Marking: every node that reads [node], directly or not, may have
   changed. *)
let mark_readers (node : node) =
  let stack = Stack.create () in
  Hashtbl.iter (fun _ (reader : node) -> Stack.push reader stack) node.readers;
  while not (Stack.is_empty stack) do
    let reader = Stack.pop stack in
    if not reader.dirty then begin
      reader.dirty <- true;
      if reader.kept then Hashtbl.replace reader.engine.dirty_kept reader.id reader;
      Hashtbl.iter (fun _ (next : node) -> Stack.push next stack) reader.readers
    end
  done

(* A saved node whose recorded reads go through an unsaved one must be
   saved again when that one's reads change. *)
let resave_readers (node : node) =
  let stack = Stack.create () in
  let seen = Hashtbl.create 8 in
  Hashtbl.iter (fun _ (reader : node) -> Stack.push reader stack) node.readers;
  while not (Stack.is_empty stack) do
    let reader = Stack.pop stack in
    if not (Hashtbl.mem seen reader.id) then begin
      Hashtbl.replace seen reader.id ();
      if reader.saved then Hashtbl.replace reader.engine.unsaved reader.id reader
      else Hashtbl.iter (fun _ (next : node) -> Stack.push next stack) reader.readers
    end
  done

let rec drop (node : node) =
  if node.alive then begin
    node.alive <- false;
    node.ops.forget ();
    let engine = node.engine in
    Hashtbl.remove engine.all node.id;
    Hashtbl.remove engine.unsaved node.id;
    Hashtbl.remove engine.dirty_kept node.id;
    if node.was_saved then engine.dropped <- node.journal_id :: engine.dropped;
    List.iter
      (fun (read : node) ->
        Hashtbl.remove read.readers node.id;
        maybe_drop read)
      node.reads;
    node.reads <- []
  end

and maybe_drop (node : node) =
  if
    node.alive && (not node.kept) && (not node.busy)
    && (not (is_frozen node))
    && Hashtbl.length node.readers = 0
  then drop node

(* Replaces a node's reads, adding it to the readers of what it reads now
   before taking it from the readers of what it no longer reads, so that a
   node read both before and after is never dropped in between. *)
let commit_reads (node : node) (reads : node list) =
  let frozen_reader = is_frozen node in
  if not frozen_reader then
    List.iter
      (fun (read : node) -> if not (is_frozen read) then Hashtbl.replace read.readers node.id node)
      reads;
  let now = Hashtbl.create (List.length reads) in
  List.iter (fun (read : node) -> Hashtbl.replace now read.id ()) reads;
  let old = node.reads in
  node.reads <- reads;
  let reads_changed = List.length old <> List.length reads || List.exists2 ( != ) old reads in
  List.iter
    (fun (read : node) ->
      if not (Hashtbl.mem now read.id) then begin
        Hashtbl.remove read.readers node.id;
        maybe_drop read
      end)
    old;
  node.height <-
    List.fold_left
      (fun height (read : node) -> if read.busy then height else max height (read.height + 1))
      0 reads;
  if reads_changed && not node.saved then resave_readers node

let record context (node : node) =
  node.read_once <- true;
  match context.frame with
  | Some frame ->
      if not (Hashtbl.mem frame.seen node.id) then begin
        Hashtbl.replace frame.seen node.id ();
        frame.read <- node :: frame.read
      end
  | None ->
      if (not node.kept) && not (is_frozen node) then begin
        node.kept <- true;
        if node.dirty then Hashtbl.replace node.engine.dirty_kept node.id node
      end

(* A cycle: every frame from the one for [node] to the newest is on it, so
   each of their results is the cycle. *)
let cycle (engine : t) (node : node) =
  let rec on_cycle acc = function
    | [] -> None
    | frame :: rest ->
        let acc = frame :: acc in
        if frame.owner == node then Some acc else on_cycle acc rest
  in
  match on_cycle [] engine.frames with
  | None -> [ node.label ]
  | Some frames ->
      let labels = List.map (fun frame -> frame.owner.label) frames in
      List.iter (fun frame -> frame.cyclic <- Some labels) frames;
      labels

(* Inputs *)

type 'value slot = Unset | Set of 'value | Stored of string

type ('key, 'value) input_cell = {
  input_key : 'key;
  input_node : node;
  mutable slot : 'value slot;
  mutable input_hash : string option;  (** The stored hash of the value, once saved *)
}

type ('key, 'value) input = {
  input_name : string;
  input_show : 'key -> string;
  input_equal : 'value -> 'value -> bool;
  input_about : 'key -> subject option;
  input_cells : (int, ('key, ('key, 'value) input_cell) Hashtbl.t) Hashtbl.t;
}

(* Restoring saved nodes needs each input and query by name. *)
type restorer = {
  restore : t -> key:string -> value:string option -> node;
  find : t -> key:string -> node option;
}

let restorers : (string, restorer) Hashtbl.t = Hashtbl.create 64
let unmarshal bytes = Marshal.from_string bytes 0

let input_value engine cell =
  match cell.slot with
  | Unset -> None
  | Set value -> Some value
  | Stored hash -> (
      match engine.get hash with
      | Some bytes ->
          let value = unmarshal bytes in
          cell.slot <- Set value;
          Some value
      | None -> None)

let rec make_input_cell :
    'key 'value. t -> ('key, 'value) input -> 'key -> ('key, 'value) input_cell =
 fun engine input key ->
  let node =
    new_node engine ~name:input.input_name
      ~label:(Printf.sprintf "%s(%s)" input.input_name (input.input_show key))
      ~is_input:true ~saved:true
  in
  let cell = { input_key = key; input_node = node; slot = Unset; input_hash = None } in
  node.ops <-
    {
      no_ops with
      forget = (fun () -> Hashtbl.remove (table input.input_cells node.engine) key);
      subject = (fun () -> input.input_about key);
      key_bytes = (fun () -> Marshal.to_string key []);
      value_hash =
        (fun () ->
          match (cell.slot, cell.input_hash) with
          | Unset, _ -> None
          | (Set _ | Stored _), Some stored -> Some stored
          | Stored stored, None -> Some stored
          | Set value, None ->
              let stored = node.engine.put (Marshal.to_string value []) in
              cell.input_hash <- Some stored;
              Some stored);
      counterpart = (fun other -> Option.map (fun c -> c.input_node) (find_input other input key));
      same =
        (fun other ->
          match find_input other.engine input key with
          | Some theirs when theirs.input_node == other -> (
              match (input_value node.engine cell, input_value other.engine theirs) with
              | Some mine, Some theirs -> input.input_equal mine theirs
              | None, None -> true
              | _ -> false)
          | _ -> false);
      current_in = (fun other -> Option.map (fun c -> c.input_node) (find_input other input key));
      copy =
        (fun target ->
          let copied = make_input_cell target input key in
          copied.slot <- cell.slot;
          copied.input_hash <- cell.input_hash;
          copied.input_node);
    };
  Hashtbl.replace (table input.input_cells engine) key cell;
  cell

and find_input : 'key 'value. t -> ('key, 'value) input -> 'key -> ('key, 'value) input_cell option
    =
 fun engine input key ->
  let own = Hashtbl.find_opt (table input.input_cells engine) key in
  let set cell = match cell.slot with Unset -> false | Set _ | Stored _ -> true in
  match own with
  | Some cell when set cell -> Some cell
  | _ -> (
      let shared =
        match engine.shared with
        | Some layer -> Hashtbl.find_opt (table input.input_cells layer) key
        | None -> None
      in
      match shared with Some cell when set cell -> Some cell | _ -> own)

let input ~name ~show ?(equal = ( = )) ?(about = fun _ -> None) () =
  let input =
    {
      input_name = name;
      input_show = show;
      input_equal = equal;
      input_about = about;
      input_cells = Hashtbl.create 4;
    }
  in
  Hashtbl.replace restorers name
    {
      restore =
        (fun engine ~key ~value ->
          let key = unmarshal key in
          let cell = make_input_cell engine input key in
          (match value with
          | Some hash ->
              cell.slot <- Stored hash;
              cell.input_hash <- Some hash
          | None -> ());
          cell.input_node);
      find =
        (fun engine ~key ->
          Option.map (fun c -> c.input_node) (find_input engine input (unmarshal key)));
    };
  input

let read context input key =
  let engine = context.engine in
  let cell =
    match find_input engine input key with
    | Some cell -> cell
    | None -> make_input_cell engine input key
  in
  record context cell.input_node;
  input_value cell.input_node.engine cell

let check_can_change (engine : t) =
  if engine.frames <> [] then invalid_arg "Incremental: an input changed while a query was running"

let change_input (engine : t) cell slot =
  let node = cell.input_node in
  if engine.is_frozen_layer && node.read_once then
    invalid_arg ("Incremental: a frozen layer's input changed after it was read: " ^ node.label);
  cell.slot <- slot;
  cell.input_hash <- None;
  engine.stamp <- engine.stamp + 1;
  node.changed_at <- engine.stamp;
  Hashtbl.replace engine.unsaved node.id node;
  mark_readers node

let own_input_cell engine input key =
  (match engine.shared with
  | Some layer -> (
      match Hashtbl.find_opt (table input.input_cells layer) key with
      | Some { slot = Set _ | Stored _; _ } ->
          invalid_arg ("Incremental: an input of the frozen layer set again: " ^ input.input_name)
      | _ -> ())
  | None -> ());
  match Hashtbl.find_opt (table input.input_cells engine) key with
  | Some cell -> cell
  | None -> make_input_cell engine input key

let set engine input key value =
  check_can_change engine;
  let cell = own_input_cell engine input key in
  match input_value engine cell with
  | Some old when input.input_equal old value -> ()
  | _ -> change_input engine cell (Set value)

let remove engine input key =
  check_can_change engine;
  match Hashtbl.find_opt (table input.input_cells engine) key with
  | Some cell -> (
      match cell.slot with Unset -> () | Set _ | Stored _ -> change_input engine cell Unset)
  | None -> ()

(* Queries *)

type 'value outcome = Value of 'value | Raised of exn

type ('key, 'value) cell = {
  key : 'key;
  node : node;
  mutable outcome : 'value outcome option;  (** [None] when not computed, or saved and not loaded *)
  mutable hash : string option;  (** The stored hash of the current outcome, when saved *)
}

type ('key, 'value) query = {
  name : string;
  show : 'key -> string;
  saved : bool;
  equal : 'value -> 'value -> bool;
  about : 'key -> subject option;
  compute : context -> 'key -> 'value;
  cells : (int, ('key, ('key, 'value) cell) Hashtbl.t) Hashtbl.t;
}

let same_outcomes query left right =
  match (left, right) with
  | Value left, Value right -> query.equal left right
  | Raised left, Raised right -> ( try left = right with Invalid_argument _ -> false)
  | _ -> false

let find_cell engine query key =
  match Hashtbl.find_opt (table query.cells engine) key with
  | Some cell -> Some cell
  | None -> (
      match engine.shared with
      | Some layer -> Hashtbl.find_opt (table query.cells layer) key
      | None -> None)

(* The outcome in memory, loading a saved one. [None] when there is none,
   or a saved one is missing from the store. *)
let loaded engine cell =
  match cell.outcome with
  | Some outcome -> Some outcome
  | None -> (
      match cell.hash with
      | None -> None
      | Some hash -> (
          match engine.get hash with
          | Some bytes ->
              let outcome = Value (unmarshal bytes) in
              cell.outcome <- Some outcome;
              Some outcome
          | None ->
              cell.hash <- None;
              None))

let rec make_cell : 'key 'value. t -> ('key, 'value) query -> 'key -> ('key, 'value) cell =
 fun engine query key ->
  let node =
    new_node engine ~name:query.name
      ~label:(Printf.sprintf "%s(%s)" query.name (query.show key))
      ~is_input:false ~saved:query.saved
  in
  let cell = { key; node; outcome = None; hash = None } in
  node.ops <-
    {
      ensure = (fun () -> ensure query cell);
      forget = (fun () -> Hashtbl.remove (table query.cells node.engine) key);
      subject = (fun () -> query.about key);
      key_bytes = (fun () -> Marshal.to_string key []);
      value_hash =
        (fun () ->
          match (cell.hash, cell.outcome) with
          | Some hash, _ -> Some hash
          | None, Some (Value value) -> (
              (* A value that holds functions cannot be saved, and is
                 computed again after loading instead. *)
              match Marshal.to_string value [] with
              | bytes ->
                  let hash = node.engine.put bytes in
                  cell.hash <- Some hash;
                  Some hash
              | exception Invalid_argument _ -> None)
          | None, (Some (Raised _) | None) -> None);
      counterpart = (fun other -> Option.map (fun c -> c.node) (find_cell other query key));
      same =
        (fun other ->
          match find_cell other.engine query key with
          | Some theirs when theirs.node == other -> (
              match (loaded node.engine cell, loaded other.engine theirs) with
              | Some mine, Some theirs -> same_outcomes query mine theirs
              | _ -> false)
          | _ -> false);
      move_to =
        (fun layer ->
          Hashtbl.remove (table query.cells node.engine) key;
          Hashtbl.remove node.engine.all node.id;
          Hashtbl.remove node.engine.unsaved node.id;
          Hashtbl.remove node.engine.dirty_kept node.id;
          node.engine <- layer;
          node.kept <- false;
          Hashtbl.replace layer.all node.id node;
          if node.saved then Hashtbl.replace layer.unsaved node.id node;
          Hashtbl.replace (table query.cells layer) key cell);
      current_in =
        (fun other ->
          let theirs =
            match find_cell other query key with Some c -> c | None -> make_cell other query key
          in
          (try ensure query theirs with Cycle _ -> ());
          Some theirs.node);
      copy =
        (fun target ->
          let copied = make_cell target query key in
          copied.outcome <- cell.outcome;
          copied.hash <- cell.hash;
          copied.node);
    };
  Hashtbl.replace (table query.cells engine) key cell;
  cell

and compute : 'key 'value. ('key, 'value) query -> ('key, 'value) cell -> unit =
 fun query cell ->
  let node = cell.node in
  let engine = node.engine in
  let first_time = node.reads = [] && cell.outcome = None && cell.hash = None in
  node.busy <- true;
  let frame = { owner = node; read = []; seen = Hashtbl.create 8; cyclic = None } in
  engine.frames <- frame :: engine.frames;
  if engine.logging then engine.log <- node.label :: engine.log;
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
  commit_reads node (List.rev frame.read);
  let changed =
    match loaded engine cell with None -> true | Some old -> not (same_outcomes query old outcome)
  in
  if changed then begin
    cell.outcome <- Some outcome;
    cell.hash <- None;
    node.changed_at <- engine.stamp;
    engine.changed <- node :: engine.changed
  end;
  node.verified_at <- engine.stamp;
  node.dirty <- false;
  engine.computed <- node :: engine.computed;
  if node.saved then Hashtbl.replace engine.unsaved node.id node;
  (* A result computed only from a frozen layer belongs to it, so every
     engine sharing the layer finds it done. Only a first result moves:
     one with readers here stays, so that they see its changes. *)
  match engine.shared with
  | Some layer
    when first_time && (not engine.is_frozen_layer) && List.for_all is_frozen node.reads
         && Hashtbl.length node.readers = 0 -> (
      match Hashtbl.find_opt (table query.cells layer) cell.key with
      | None -> node.ops.move_to layer
      | Some _ -> ())
  | _ -> ()

and verify : 'key 'value. ('key, 'value) query -> ('key, 'value) cell -> unit =
 fun query cell ->
  let node = cell.node in
  let engine = node.engine in
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
        if is_frozen read then stale rest
        else if read.busy then true
        else begin
          read.ops.ensure ();
          read.changed_at > node.verified_at || stale rest
        end
  in
  let needs =
    match stale node.reads with
    | needs -> needs || frame.cyclic <> None
    | exception exception_ ->
        finish ();
        raise exception_
  in
  finish ();
  if needs then compute query cell
  else begin
    node.dirty <- false;
    node.verified_at <- engine.stamp
  end

and ensure : 'key 'value. ('key, 'value) query -> ('key, 'value) cell -> unit =
 fun query cell ->
  let node = cell.node in
  if node.busy then ()
  else
    match loaded node.engine cell with
    | None ->
        (* Never computed, or a saved result the store no longer has. A lost
           result is computed again and counts as changed, so what read it is
           checked again too. *)
        let lost = node.reads <> [] in
        compute query cell;
        if lost then mark_readers node
    | Some _ -> if node.dirty then verify query cell

let query ~name ~show ?(saved = false) ?(equal = ( = )) ?(about = fun _ -> None) compute =
  let query = { name; show; saved; equal; about; compute; cells = Hashtbl.create 4 } in
  if saved then
    Hashtbl.replace restorers name
      {
        restore =
          (fun engine ~key ~value ->
            let cell = make_cell engine query (unmarshal key) in
            cell.hash <- value;
            cell.node);
        find =
          (fun engine ~key -> Option.map (fun c -> c.node) (find_cell engine query (unmarshal key)));
      };
  query

let demand context query key =
  let engine = context.engine in
  let cell =
    match find_cell engine query key with Some cell -> cell | None -> make_cell engine query key
  in
  let node = cell.node in
  if node.busy then begin
    let labels = cycle node.engine node in
    record context node;
    raise (Cycle labels)
  end;
  ensure query cell;
  record context node;
  match loaded node.engine cell with
  | Some (Value value) -> value
  | Some (Raised exception_) -> raise exception_
  | None -> invalid_arg ("Incremental: no result for " ^ node.label)

(* Engines *)

type change = { computed : node list; changed : node list }

let stabilize (engine : t) =
  check_can_change engine;
  let rec loop () =
    if Hashtbl.length engine.dirty_kept > 0 then begin
      let pending =
        List.sort
          (fun (a : node) (b : node) -> compare a.id b.id)
          (Hashtbl.fold (fun _ node acc -> node :: acc) engine.dirty_kept [])
      in
      Hashtbl.reset engine.dirty_kept;
      List.iter (fun node -> if node.alive && node.dirty then node.ops.ensure ()) pending;
      loop ()
    end
  in
  loop ();
  let change = { computed = List.rev engine.computed; changed = List.rev engine.changed } in
  engine.computed <- [];
  engine.changed <- [];
  change

let release (engine : t) query key =
  match Hashtbl.find_opt (table query.cells engine) key with
  | Some cell ->
      cell.node.kept <- false;
      maybe_drop cell.node
  | None -> ()

let executed engine = List.rev engine.log
let clear_log engine = engine.log <- []

(* Nodes *)

let label (node : node) = node.label
let subject (node : node) = node.ops.subject ()
let reads (node : node) = node.reads

let readers (node : node) =
  List.sort
    (fun (a : node) (b : node) -> compare a.id b.id)
    (Hashtbl.fold (fun _ reader acc -> reader :: acc) node.readers [])

let by_id nodes = List.sort (fun (a : node) (b : node) -> compare a.id b.id) nodes
let nodes (engine : t) = by_id (Hashtbl.fold (fun _ node acc -> node :: acc) engine.all [])
let counterpart (node : node) other = node.ops.counterpart other
let same_outcome (left : node) right = left.ops.same right

(* Saving *)

type saved_node = {
  id : int;
  name : string;
  key : string;
  value : string option;
  reads : reference list;
  kept : bool;
}

and reference = Own of int | Frozen of string * string

let set_store engine ~put ~get =
  engine.put <- put;
  engine.get <- get

(* A saved node's reads, through every unsaved node, to the saved nodes and
   inputs they reach. *)
let journal_id (engine : t) (node : node) =
  if node.journal_id = 0 then begin
    node.journal_id <- engine.next_journal_id;
    engine.next_journal_id <- engine.next_journal_id + 1
  end;
  node.journal_id

(* A read of a frozen layer never changes, so it matters only for questions
   about dependencies, and only a saved one can be found again. *)
let frozen_reference (read : node) =
  if read.saved || read.is_input then [ Frozen (read.name, read.ops.key_bytes ()) ] else []

let saved_reads engine memo (node : node) =
  let rec through (node : node) =
    match Hashtbl.find_opt memo node.id with
    | Some references -> references
    | None ->
        let references =
          List.concat_map
            (fun (read : node) ->
              if is_frozen read then frozen_reference read
              else if read.saved then [ Own (journal_id engine read) ]
              else through read)
            node.reads
        in
        let unique = List.sort_uniq compare references in
        Hashtbl.replace memo node.id unique;
        unique
  in
  List.sort_uniq compare
    (List.concat_map
       (fun (read : node) ->
         if is_frozen read then frozen_reference read
         else if read.saved then [ Own (journal_id engine read) ]
         else through read)
       node.reads)

let saved_node engine memo (node : node) =
  node.was_saved <- true;
  {
    id = journal_id engine node;
    name = node.name;
    key = node.ops.key_bytes ();
    value = node.ops.value_hash ();
    reads = saved_reads engine memo node;
    kept = node.kept;
  }

let changes_to_save (engine : t) =
  let memo = Hashtbl.create 64 in
  let changed =
    by_id
      (Hashtbl.fold (fun _ node acc -> if node.alive then node :: acc else acc) engine.unsaved [])
  in
  Hashtbl.reset engine.unsaved;
  let dropped = List.rev engine.dropped in
  engine.dropped <- [];
  (List.map (saved_node engine memo) changed, dropped)

let everything_to_save (engine : t) =
  let memo = Hashtbl.create 1024 in
  Hashtbl.reset engine.unsaved;
  engine.dropped <- [];
  List.filter_map
    (fun (node : node) -> if node.saved then Some (saved_node engine memo node) else None)
    (nodes engine)

let restore (engine : t) (saved : saved_node list) =
  let made = Hashtbl.create (List.length saved) in
  List.iter
    (fun (s : saved_node) ->
      match Hashtbl.find_opt restorers s.name with
      | Some restorer -> (
          match restorer.restore engine ~key:s.key ~value:s.value with
          | node ->
              node.journal_id <- s.id;
              engine.next_journal_id <- max engine.next_journal_id (s.id + 1);
              Hashtbl.replace made s.id (node, s)
          | exception _ -> ())
      | None -> ())
    saved;
  let find = function
    | Own id -> Some (Option.map fst (Hashtbl.find_opt made id))
    | Frozen (name, key) -> (
        (* A frozen node that cannot be found is left out of the reads: it
           can never change, so no result depends on finding it. *)
        match (engine.shared, Hashtbl.find_opt restorers name) with
        | Some layer, Some restorer -> (
            match restorer.find layer ~key with
            | Some node -> Some (Some node)
            | None -> None
            | exception _ -> None)
        | _ -> None)
  in
  (* A node that reads an own node that is missing is left out, and so is
     everything that reads it, since its result could not be checked. *)
  let reads_of = Hashtbl.create (Hashtbl.length made) in
  let broken = Hashtbl.create 8 in
  Hashtbl.iter
    (fun id (_, (s : saved_node)) ->
      let found = List.filter_map find s.reads in
      if List.exists Option.is_none found then Hashtbl.replace broken id ()
      else Hashtbl.replace reads_of id (List.filter_map Fun.id found))
    made;
  let readers_of = Hashtbl.create (Hashtbl.length made) in
  Hashtbl.iter
    (fun id (_, (s : saved_node)) ->
      List.iter
        (function
          | Own read ->
              Hashtbl.replace readers_of read
                (id :: Option.value (Hashtbl.find_opt readers_of read) ~default:[])
          | Frozen _ -> ())
        s.reads)
    made;
  let rec spread id =
    List.iter
      (fun reader ->
        if not (Hashtbl.mem broken reader) then begin
          Hashtbl.replace broken reader ();
          spread reader
        end)
      (Option.value (Hashtbl.find_opt readers_of id) ~default:[])
  in
  List.iter spread (Hashtbl.fold (fun id () acc -> id :: acc) broken []);
  Hashtbl.iter
    (fun id (node, (s : saved_node)) ->
      if Hashtbl.mem broken id then begin
        node.alive <- false;
        node.ops.forget ();
        Hashtbl.remove engine.all node.id
      end
      else begin
        let reads = Hashtbl.find reads_of id in
        node.reads <- reads;
        List.iter
          (fun (read : node) ->
            if not (is_frozen read) then Hashtbl.replace read.readers node.id node)
          reads;
        node.kept <- s.kept;
        node.was_saved <- true
      end)
    made;
  let rec height (node : node) =
    if node.height > 0 || node.reads = [] then node.height
    else begin
      node.height <-
        1
        + List.fold_left
            (fun h read -> if is_frozen read then h else max h (height read))
            0 node.reads;
      node.height
    end
  in
  Hashtbl.iter (fun _ (node, _) -> if node.alive then ignore (height node)) made;
  Hashtbl.reset engine.unsaved;
  engine.dropped <- []

let engine_of context = context.engine

let fork (engine : t) =
  check_can_change engine;
  let copy = make_engine ~logging:engine.logging ~shared:engine.shared ~is_frozen_layer:false in
  copy.stamp <- engine.stamp;
  copy.put <- engine.put;
  copy.get <- engine.get;
  let originals = nodes engine in
  let made = Hashtbl.create (List.length originals) in
  List.iter (fun (node : node) -> Hashtbl.replace made node.id (node.ops.copy copy)) originals;
  let mapped (read : node) =
    match Hashtbl.find_opt made read.id with Some n -> n | None -> read
  in
  List.iter
    (fun (node : node) ->
      let twin = Hashtbl.find made node.id in
      twin.reads <- List.map mapped node.reads;
      List.iter
        (fun (read : node) ->
          if not (is_frozen read) then Hashtbl.replace read.readers twin.id twin)
        twin.reads;
      twin.height <- node.height;
      twin.dirty <- node.dirty;
      twin.changed_at <- node.changed_at;
      twin.verified_at <- node.verified_at;
      twin.kept <- node.kept;
      twin.read_once <- node.read_once;
      if twin.kept && twin.dirty then Hashtbl.replace copy.dirty_kept twin.id twin;
      if twin.saved then Hashtbl.replace copy.unsaved twin.id twin)
    originals;
  copy

let current_in (node : node) other = node.ops.current_in other
let bring_up_to_date (node : node) = node.ops.ensure ()
let is_input (node : node) = node.is_input
