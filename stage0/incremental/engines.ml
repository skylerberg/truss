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
      if cell.node.kept then begin
        cell.node.kept <- false;
        Hashtbl.replace engine.unsaved cell.node.id cell.node
      end;
      drop_or_wait engine cell.node;
      sweep engine
  | None -> ()

let executed engine = List.rev engine.log
let clear_log engine = engine.log <- []
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
