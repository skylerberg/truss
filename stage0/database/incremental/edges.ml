open Nodes

(* A node as an engine sees it: its own copy, if it has made one. *)
let resolve engine (node : node) =
  if node.engine == engine then node
  else match Hashtbl.find_opt engine.shadows node.id with Some own -> own | None -> node

(* Collection. A node is necessary if it is a root or a necessary node reads
   it; an unnecessary node is collected, with what only it read. That is done
   only once no query runs: a query that is still running has read nodes
   that do not yet count it as a reader. A copy of a base's node is never
   collected, since the base's readers may read it. *)

let defer_collection engine (node : node) =
  if node.engine == engine && node.below = None && not node.root then
    engine.candidates <- node :: engine.candidates

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

(* A result is collectable, and an input only while it is not set: one that
   is set holds what the database gave it. *)
let collectable (node : node) =
  match node.cell with
  | Input (_, { slot = Unset; _ }) | Result _ -> true
  | Input _ | Unfilled -> false

let rec collect engine (node : node) =
  if
    node.alive && (not node.root) && (not node.busy) && node.below = None
    && Hashtbl.length node.readers = 0
    && collectable node
  then begin
    node.alive <- false;
    forget engine node;
    Hashtbl.remove engine.own node.id;
    Hashtbl.remove engine.unsaved node.id;
    if node.written <> Unwritten then
      engine.collected <- (name node, key_bytes node) :: engine.collected;
    engine.tally.collections <- engine.tally.collections + 1;
    let reads = node.reads in
    node.reads <- [];
    List.iter
      (fun read ->
        remove_reader engine read node;
        collect_or_defer engine read)
      reads
  end

and collect_or_defer engine (node : node) =
  if engine.frames = [] then (if node.engine == engine then collect engine node)
  else defer_collection engine node

let rec sweep engine =
  if engine.frames = [] then
    match engine.candidates with
    | [] -> ()
    | candidates ->
        engine.candidates <- [];
        List.iter (collect engine) candidates;
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
        defer_collection engine read
      end)
    old

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
      own.root <- base.root;
      own.written <- In_whole;
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
  let in_phase (reader : node) = match phase with Some p -> reader.phase = p | None -> true in
  let own =
    Hashtbl.fold
      (fun _ (reader : node) readers -> if in_phase reader then reader :: readers else readers)
      node.readers []
  in
  match node.below with
  | None -> own
  | Some base ->
      let from table readers =
        Hashtbl.fold
          (fun _ (reader : node) readers ->
            if (not (in_phase reader)) || Hashtbl.mem engine.shadows reader.id then readers
            else shadow engine reader :: readers)
          table readers
      in
      List.fold_left
        (fun readers (other : t) ->
          match Hashtbl.find_opt other.foreign base.id with
          | Some table -> from table readers
          | None -> readers)
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

(* Records a read. A query's read is an edge. A driver's read makes the
   result a root, unless the driver only observes: a root is part of the
   state, so it is written, though the node's result is as it was. A base's
   node is copied into the engine to be its root there, since a base never
   changes. *)
let record_read (context : context) (node : node) =
  match context.frame with
  | Some frame ->
      if not (Hashtbl.mem frame.seen node.id) then begin
        Hashtbl.replace frame.seen node.id ();
        Dynarray.add_last frame.read node
      end
  | None ->
      let engine = context.engine in
      if (not engine.frozen) && (not context.observing) && not node.root then begin
        let own = if node.engine == engine then node else shadow engine node in
        if not own.root then begin
          own.root <- true;
          Hashtbl.replace engine.unsaved own.id own
        end
      end

(* A cycle: every frame from the one for [node] to the newest is on it, so
   each of their results is the cycle. *)
let cycle engine (node : node) =
  let rec on_cycle frames = function
    | [] -> None
    | frame :: rest ->
        let frames = frame :: frames in
        if frame.owner == node then Some frames else on_cycle frames rest
  in
  match on_cycle [] engine.frames with
  | None -> [ label node ]
  | Some frames ->
      let labels = List.map (fun frame -> label frame.owner) frames in
      List.iter (fun frame -> frame.cyclic <- Some labels) frames;
      labels
