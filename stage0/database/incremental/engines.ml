open Nodes
open Edges
open Values
open Update
open Declare

type change = { computed : node list; changed : node list }

let stabilize engine =
  check_can_change engine;
  sweep engine;
  settle engine;
  let change =
    { computed = Dynarray.to_list engine.computed; changed = Dynarray.to_list engine.changed }
  in
  Dynarray.clear engine.computed;
  Dynarray.clear engine.changed;
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

let unroot engine (query : ('key, 'value) query) key =
  match Hashtbl.find_opt (result_cells engine query) key with
  | Some cell ->
      if cell.node.root then begin
        cell.node.root <- false;
        Hashtbl.replace engine.unsaved cell.node.id cell.node
      end;
      collect_or_defer engine cell.node;
      sweep engine
  | None -> ()

let executed engine = List.map label (Dynarray.to_list engine.log)

let result_label (query : ('key, 'value) query) key =
  Printf.sprintf "%s(%s)" query.name (query.show key)

let computed (type key value) engine (query : (key, value) query) : key list =
  List.filter_map
    (fun (node : node) ->
      match node.cell with
      | Result (stored_query, cell) when stored_query.number = query.number -> (
          match Type.Id.provably_equal stored_query.cells query.cells with
          | Some Equal -> Some (cell.key : key)
          | None -> None)
      | Result _ | Input _ | Unfilled -> None)
    (Dynarray.to_list engine.log)

let clear_log engine = Dynarray.clear engine.log
let by_id nodes = List.sort (fun (a : node) (b : node) -> compare a.id b.id) nodes
let differing engine = by_id (Hashtbl.fold (fun _ node nodes -> node :: nodes) engine.own [])
let count engine = Hashtbl.length engine.own

(* The engine's own nodes and those of each base that [skip] does not
   exclude and the engine has not replaced. *)
let own_and_inherited engine ~skip =
  let own = Hashtbl.fold (fun _ node nodes -> node :: nodes) engine.own [] in
  by_id
    (List.fold_left
       (fun nodes (base : t) ->
         if skip base then nodes
         else
           Hashtbl.fold
             (fun _ (node : node) nodes ->
               if Hashtbl.mem engine.shadows node.id then nodes else node :: nodes)
             base.own nodes)
       own engine.bases)

let unshared engine other =
  own_and_inherited engine ~skip:(fun base -> base.fixed || List.memq base other.bases)

(* The state's nodes, apart from its fixed bases': the engine's own, and
   those of an earlier state it has not replaced. *)
let nodes engine = own_and_inherited engine ~skip:(fun base -> base.fixed)
let reads = current_reads

(* What reads a node, without copying anything: a base's reader that the
   engine has not copied reads the engine's copy as it read the base's
   node. *)
let readers engine (node : node) =
  let below = if node.engine == engine then node.below else Some node in
  let own =
    if node.engine == engine then
      Hashtbl.fold (fun _ reader readers -> reader :: readers) node.readers []
    else
      match Hashtbl.find_opt engine.foreign node.id with
      | Some table -> Hashtbl.fold (fun _ reader readers -> reader :: readers) table []
      | None -> []
  in
  let readers =
    match below with
    | None -> own
    | Some base ->
        let from table readers =
          Hashtbl.fold
            (fun _ (reader : node) readers ->
              if Hashtbl.mem engine.shadows reader.id then readers else reader :: readers)
            table readers
        in
        List.fold_left
          (fun readers (other : t) ->
            match Hashtbl.find_opt other.foreign base.id with
            | Some table -> from table readers
            | None -> readers)
          (if base.engine == engine then own else from base.readers own)
          engine.bases
  in
  by_id readers

(* The same query and key in another engine, computed there if it has none.
   The other engine only observes it, so comparing two states makes no root
   in either. *)
let current_in (node : node) other =
  match node.cell with
  | Input (input, cell) ->
      Option.map (fun cell -> cell.input_node) (find_input other input cell.input_key)
  | Result (query, cell) ->
      if other.frozen then Option.map (fun cell -> cell.node) (find_result other query cell.key)
      else Some (observed_node other query cell.key)
  | Unfilled -> None

(* Whether two nodes of one query or input and key, each in its engine,
   hold equal results. The nodes' own cells are compared, so a node that
   was collected since still answers. *)
let same_outcome engine (left : node) other (right : node) =
  match (left.cell, right.cell) with
  | Input (input, mine), Input (other_input, theirs) -> (
      match Type.Id.provably_equal input.input_cells other_input.input_cells with
      | Some Type.Equal -> (
          match (input_value engine mine, input_value other theirs) with
          | Some mine, Some theirs -> input.input_equal mine theirs
          | None, None -> true
          | _ -> false)
      | None -> false)
  | Result (query, mine), Result (other_query, theirs) -> (
      match Type.Id.provably_equal query.cells other_query.cells with
      | Some Type.Equal -> (
          match (hash_of left.fingerprint, hash_of right.fingerprint) with
          | Some mine, Some theirs when mine = theirs -> true
          | _ -> (
              match (load engine mine, load other theirs) with
              | Some mine, Some theirs -> same_outcomes query mine theirs
              | _ -> false))
      | None -> false)
  | _ -> false

(* Whether the store still has the value of every input of the state,
   apart from its fixed bases'. *)
let inputs_stored engine =
  List.for_all
    (fun (holder : t) ->
      Hashtbl.fold
        (fun _ (node : node) stored ->
          stored
          &&
          match node.cell with
          | Input (_, { slot = Stored; _ }) -> stored_bytes holder node <> None
          | Input _ | Result _ | Unfilled -> true)
        holder.own true)
    (engine :: List.filter (fun (base : t) -> not base.fixed) engine.bases)
