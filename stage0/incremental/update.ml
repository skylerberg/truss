open Nodes
open Edges
open Values

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
  | Some store when query.saved && query.portable -> (
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
        (* Nothing reads it and no request kept it, so it is dropped: left
           marked, it would be written and opened as if it were current. *)
        List.iter
          (fun (node : node) ->
            if node.alive && node.marked then
              if wanted node then ensure engine node else consider engine node;
            sweep engine)
          marked;
        sweep engine;
        settle engine

let check_can_change engine =
  if engine.frozen then invalid_arg "Incremental: a frozen engine cannot change";
  if engine.frames <> [] then invalid_arg "Incremental: an input changed while a query was running"
