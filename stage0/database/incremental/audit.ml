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
    within_audit := true;
    let fresh =
      Fun.protect
        ~finally:(fun () -> within_audit := false)
        (fun () -> create ~bases:(if include_bases then [] else engine.bases) ())
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
    if include_bases then
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
          | Result (query, cell)
            when node.alive && match before with Some phase -> node.phase < phase | None -> true
            -> (
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
  let problems = ref [] in
  let table = !remembered in
  for index = 0 to Weak.length table - 1 do
    match Weak.get table index with
    | Some engine
      when (not engine.frozen) && engine.audited <> max_int && engine.activity <> engine.audited
           && engine.frames = [] ->
        problems := audit engine @ !problems
    | _ -> ()
  done;
  !problems
