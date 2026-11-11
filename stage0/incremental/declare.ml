open Nodes
open Edges
open Values
open Update

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
  (match context.frame with None when not engine.frozen -> settle ~through:0 engine | _ -> ());
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
        match input_value engine cell with
        | Some old -> input.input_equal old value
        | None | (exception Lost _) -> false)
    | None -> false
  in
  if not same then change engine (own_input engine input key) (Set value)

let remove engine (input : ('key, 'value) input) key =
  check_can_change engine;
  match find_input engine input key with
  | Some { slot = Set _ | Stored; _ } -> change engine (own_input engine input key) Unset
  | Some { slot = Unset; _ } | None -> ()

let query ~name ~show ~phase ?(saved = false) ?(portable = false) ?(equal = ( = ))
    ?(about = fun _ -> None) compute =
  if phase < 1 || phase >= phases then invalid_arg "Incremental.query: no such phase";
  incr numbers;
  let query =
    {
      number = !numbers;
      name;
      show;
      phase;
      saved;
      portable;
      equal;
      about;
      compute;
      cells = Type.Id.make ();
    }
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
  | None -> if not engine.frozen then settle ~through:query.phase engine);
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

(* The result a state holds for a query and key, if nothing that changed
   could have reached it. The phases before the query's are brought up to
   date, and what reads their changes within the query's phase is marked,
   so a result that is not marked is current. Nothing of the query's phase
   is computed, no read is recorded, and the result is not kept. *)
let known (context : context) (query : ('key, 'value) query) (key : 'key) : 'value option =
  let engine = context.engine in
  if context.frame <> None then invalid_arg "Incremental.known: called while a query runs";
  if not engine.frozen then begin
    settle ~through:(query.phase - 1) engine;
    mark_seeds engine query.phase
  end;
  match find_result engine query key with
  | Some cell when not (cell.node.marked || cell.node.busy) -> (
      match load engine cell with
      | Some (Value value) -> Some value
      | Some (Raised _) | None -> None)
  | Some _ | None -> None
