open Nodes

let resolve engine (node : node) =
  if node.engine == engine then node
  else match Hashtbl.find_opt engine.shadows node.id with Some own -> own | None -> node

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

let readers_here engine (node : node) ~phase =
  let in_phase (reader : node) =
    match phase with Some wanted_phase -> reader.phase = wanted_phase | None -> true
  in
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

let seed engine (node : node) =
  List.iter
    (fun (reader : node) ->
      if not reader.marked then begin
        engine.seeds.(reader.phase) <- reader :: engine.seeds.(reader.phase);
        engine.waiting <- engine.waiting + 1
      end)
    (readers_here engine node ~phase:None)

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
        let own =
          if node.engine == engine then Some node
          else
            match Hashtbl.find_opt engine.shadows node.id with
            | Some own -> Some own
            | None -> if node.engine.fixed then None else Some (shadow engine node)
        in
        match own with
        | Some own when not own.root ->
            own.root <- true;
            Hashtbl.replace engine.unsaved own.id own
        | Some _ | None -> ()
      end

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
