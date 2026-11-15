open Nodes
open Edges
open Values
open Update

let input ~name ~show ?(equal = ( = )) ?(about = fun _ -> None) () =
  check_not_sealed name;
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
              Hashtbl.replace engine.unwritten_nodes cell.input_node.id cell.input_node;
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
      record_read context cell.input_node;
      input_value engine cell
  | None ->
      if engine.frozen then None
      else begin
        let cell = make_input engine input key ~below:None in
        Hashtbl.replace engine.unwritten_nodes cell.input_node.id cell.input_node;
        record_read context cell.input_node;
        if context.frame = None && context.observing then begin
          defer_collection engine cell.input_node;
          sweep engine
        end;
        None
      end

let change engine (cell : ('key, 'value) input_cell) slot =
  let node = cell.input_node in
  cell.slot <- slot;
  forget_fingerprint node;
  node.changed_at <- tick engine;
  engine.activity <- engine.activity + 1;
  Hashtbl.replace engine.unwritten_nodes node.id node;
  seed engine node

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
  check_not_sealed name;
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
      record_read context node;
      raise (Cycle labels)
    end;
    ensure_result engine query cell
  end;
  record_read context node;
  let result =
    match value engine query cell with value -> Ok value | exception raised -> Error raised
  in
  (match (context.frame, result) with
  | None, _ ->
      if context.observing then defer_collection engine node;
      sweep engine
  | Some frame, Error (Cycle labels) -> if frame.cyclic = None then frame.cyclic <- Some labels
  | Some _, _ -> ());
  match result with Ok value -> value | Error exception_ -> raise exception_

let observed_node engine (query : ('key, 'value) query) (key : 'key) : node =
  settle ~through:query.phase engine;
  let cell =
    match find_result engine query key with
    | Some cell -> cell
    | None -> make_result engine query key ~below:None
  in
  if cell.node.engine == engine then ensure_result engine query cell;
  (try ignore (value engine query cell) with Lost _ as lost -> raise lost | _ -> ());
  let node = match find_result engine query key with Some cell -> cell.node | None -> cell.node in
  defer_collection engine node;
  sweep engine;
  node
