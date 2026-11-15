open Nodes
open Edges
open Values
open Update
open Declare
open Engines

let describe_outcome (outcome : 'value outcome option) =
  match outcome with
  | None -> "nothing"
  | Some (Value _) -> "a value"
  | Some (Raised exception_) -> "raising " ^ Printexc.to_string exception_

let audit ?(include_bases = false) ?before engine =
  if engine.frozen then []
  else begin
    check_can_change engine;
    sweep engine;
    settle engine;
    let fresh = create ~bases:(if include_bases then [] else engine.bases) () in
    fresh.store <-
      Option.map
        (fun store ->
          {
            store with
            put = Blake3.hash;
            find_fact = (fun _ -> None);
            add_fact = (fun _ _ -> ());
            find_reads = (fun _ -> None);
            add_reads = (fun _ _ -> ());
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
    if include_bases then
      List.iter
        (fun (base : t) ->
          Hashtbl.iter
            (fun _ (node : node) -> if not (Hashtbl.mem engine.shadows node.id) then replay node)
            base.own)
        (List.rev engine.bases);
    let own = differing engine in
    List.iter replay own;
    List.filter_map
      (fun (node : node) ->
        match node.cell with
        | Result (query, cell)
          when node.alive && match before with Some phase -> node.phase < phase | None -> true -> (
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
  end
