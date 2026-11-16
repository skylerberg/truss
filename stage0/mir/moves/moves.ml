type path = { local : Mir.local; projections : Mir.projection list }

module Place_table = Hashtbl.Make (Structural_key.Make (struct
  type t = path
end))

let path_of_place (place : Mir.place) =
  match place.root with
  | Constant _ | Literal _ -> None
  | Local local -> Some { local; projections = place.projections }

let rec is_prefix prefix projections =
  match (prefix, projections) with
  | [], _ -> true
  | projection :: prefix, other :: projections -> projection = other && is_prefix prefix projections
  | _ :: _, [] -> false

let is_inside ~outer inner =
  outer.local = inner.local && is_prefix outer.projections inner.projections

let overlaps first second = is_inside ~outer:first second || is_inside ~outer:second first

type use = {
  place : Mir.place;
  origin : Core.origin;
  moves : bool;
  operand : Mir.operand option;
  passed : Types.mode option;
}

let list_operand_uses ?passed ~moving ~by_value (operand : Mir.operand) =
  match operand with
  | Use { place; type_; origin; _ } | Take { place; type_; origin } ->
      [ { place; origin; moves = by_value && moving type_; operand = Some operand; passed } ]
  | Borrow { place; type_; origin; _ } ->
      let moves = by_value && Option.is_some passed && moving type_ in
      [ { place; origin; moves; operand = Some operand; passed } ]
  | Constant _ -> []

let read ~origin place = { place; origin; moves = false; operand = None; passed = None }

let list_rvalue_uses ~moving ~origin (rvalue : Mir.rvalue) =
  let by_value = List.concat_map (list_operand_uses ~moving ~by_value:true)
  and reads = List.concat_map (list_operand_uses ~moving ~by_value:false) in
  match rvalue with
  | Operand operand | To_any { value = operand; _ } -> by_value [ operand ]
  | Operation { operands; _ } | Array operands -> by_value operands
  | Construct { fields; _ } -> by_value (List.filter_map snd fields)
  | Compare { left; right; _ } -> reads [ left; right ]
  | Not operand | Convert { value = operand; _ } | Copy operand -> reads [ operand ]
  | Is_variant { place; _ } -> [ read ~origin place ]
  | Lambda { captures; _ } ->
      List.map (fun (capture : Mir.capture) -> read ~origin capture.place) captures
  | Function_value _ | Value_parameter _ | Specification _ -> []

let list_call_uses ~moving (call : Mir.call) =
  (match call.callee with
    | Indirect operand -> list_operand_uses ~moving ~by_value:false operand
    | _ -> [])
  @ List.concat_map
      (function
        | Mir.Passed { mode; value; _ } ->
            list_operand_uses ~passed:mode ~moving ~by_value:(mode = Own) value
        | Default -> [])
      call.arguments

let uses ~moving (statement : Mir.Graph.statement) =
  let origin = statement.origin in
  match statement.kind with
  | Assign { value; _ } -> list_rvalue_uses ~moving ~origin value
  | Call { call; _ } | Lend { call; _ } | Slice { call; _ } | Template { call; _ } ->
      list_call_uses ~moving call
  | Assert operand | Echo operand -> list_operand_uses ~moving ~by_value:false operand
  | Provide { provided; _ } ->
      List.concat_map
        (fun (provided : Mir.provided) -> list_operand_uses ~moving ~by_value:false provided.value)
        provided
  | Live _ | Dead _ | Provide_end | Loan_start _ | Loan_end _ | Ghost_assert _ | Matched _ | Proof _
    ->
      []

let rec list_yielded_uses ~moving ~owns : Mir.yielded -> use list = function
  | Part
      (Borrow { place = { root = Local local; projections = [] } as place; type_; origin; _ } as
       operand)
    when owns local ->
      [ { place; origin; moves = moving type_; operand = Some operand; passed = None } ]
  | Part operand -> list_operand_uses ~moving ~by_value:true operand
  | Built { fields; _ } ->
      List.concat_map
        (fun (_, field) -> Option.fold ~none:[] ~some:(list_yielded_uses ~moving ~owns) field)
        fields

let list_terminator_uses ~moving ~owns (basic : Mir.Graph.basic_block) =
  let origin = basic.terminator_origin in
  match basic.terminator with
  | Branch { condition; _ } -> list_operand_uses ~moving ~by_value:false condition
  | For { iteration = Range { start; stop; _ }; _ } ->
      List.concat_map (list_operand_uses ~moving ~by_value:false) [ start; stop ]
  | For { iteration = Pull { cursor; _ }; _ } -> [ read ~origin cursor ]
  | Yield { part; _ } -> list_yielded_uses ~moving ~owns part
  | Return (Some operand) | Cancel { returned = Some (operand, _); _ } ->
      list_operand_uses ~moving ~by_value:true operand
  | Resume { winner; _ } -> [ read ~origin { root = Local winner; projections = [] } ]
  | Goto _ | Fork _ | Join _ | Iteration_end _
  | Return None
  | Cancel { returned = None; _ }
  | Unreachable | Written_unreachable | Todo ->
      []

let list_moved uses =
  List.filter_map (fun use -> if use.moves then Some (use.place, use.origin) else None) uses

let list_moves ~moving statement = list_moved (uses ~moving statement)

let list_inits (statement : Mir.Graph.statement) : Mir.place list =
  match statement.kind with
  | Assign { target; _ } -> [ target ]
  | Call { destination; _ } -> Option.to_list destination
  | Lend { part; _ } -> [ { root = Local part; projections = [] } ]
  | Slice { destination; _ } | Template { destination; _ } -> [ destination ]
  | Live _ | Dead _ | Assert _ | Echo _ | Provide _ | Provide_end | Loan_start _ | Loan_end _
  | Ghost_assert _ | Matched _ | Proof _ ->
      []

let list_ended (statement : Mir.Graph.statement) =
  match statement.kind with Dead locals -> locals | _ -> []

let list_terminator_moves ~moving ~owns basic =
  list_moved (list_terminator_uses ~moving ~owns basic)

type t = {
  paths : path array;
  positions : int Place_table.t;
  of_local : (Mir.local, int list) Hashtbl.t;
  inside : int list array;
  parameters : Mir.local list;
  is_owner : Mir.local -> bool;
  is_lent : Mir.local -> bool;
  is_moving : Types.ty -> bool;
  loop_parts : (Mir.Graph.block, Mir.local list) Hashtbl.t;
  entries : state array;
  mutable flagged : int list;
}

and state = {
  maybe_holds : bool array;
  maybe_empty : bool array;
  moved_at : Core.origin list array;
}

type status = Holds | Empty | Maybe

let index analysis path = Place_table.find_opt analysis.positions path

let list_affected analysis place =
  match path_of_place place with
  | None -> []
  | Some outer ->
      List.filter
        (fun position -> is_inside ~outer analysis.paths.(position))
        (Option.value (Hashtbl.find_opt analysis.of_local outer.local) ~default:[])

let list_affected_by_local analysis local =
  list_affected analysis { root = Local local; projections = [] }

let copy state =
  {
    maybe_holds = Array.copy state.maybe_holds;
    maybe_empty = Array.copy state.maybe_empty;
    moved_at = Array.copy state.moved_at;
  }

let set_empty ?origin state positions =
  List.iter
    (fun position ->
      state.maybe_holds.(position) <- false;
      state.maybe_empty.(position) <- true;
      state.moved_at.(position) <- Option.to_list origin)
    positions

let set_holds state positions =
  List.iter
    (fun position ->
      state.maybe_holds.(position) <- true;
      state.maybe_empty.(position) <- false;
      state.moved_at.(position) <- [])
    positions

let apply_effects analysis state ~moves ~inits ~ends =
  List.iter (fun (place, origin) -> set_empty ~origin state (list_affected analysis place)) moves;
  List.iter (fun place -> set_holds state (list_affected analysis place)) inits;
  List.iter (fun local -> set_empty state (list_affected_by_local analysis local)) ends

let apply_moves analysis state statement =
  apply_effects analysis state
    ~moves:(list_moves ~moving:analysis.is_moving statement)
    ~inits:[] ~ends:[]

let owns analysis local = analysis.is_owner local
let is_lent_mut analysis local = analysis.is_lent local
let list_statement_uses analysis statement = uses ~moving:analysis.is_moving statement
let move_out analysis state place ~origin = set_empty ~origin state (list_affected analysis place)

let list_moved_at analysis state path =
  match index analysis path with Some position -> state.moved_at.(position) | None -> []

let list_given_by statement = List.filter_map path_of_place (list_inits statement)

let may_be_empty analysis state (path : path) =
  List.find_opt
    (fun (tracked : path) ->
      overlaps tracked path && state.maybe_empty.(Place_table.find analysis.positions tracked))
    (List.sort
       (fun (left : path) (right : path) ->
         compare (List.length left.projections) (List.length right.projections))
       (List.map
          (fun position -> analysis.paths.(position))
          (Option.value (Hashtbl.find_opt analysis.of_local path.local) ~default:[])))

let apply analysis state statement =
  apply_effects analysis state
    ~moves:(list_moves ~moving:analysis.is_moving statement)
    ~inits:(list_inits statement) ~ends:(list_ended statement)

let apply_terminator_moves analysis state basic =
  apply_effects analysis state
    ~moves:(list_terminator_moves ~moving:analysis.is_moving ~owns:analysis.is_owner basic)
    ~inits:[] ~ends:[]

let find_status analysis state path =
  Option.map
    (fun position ->
      match (state.maybe_holds.(position), state.maybe_empty.(position)) with
      | true, false -> Holds
      | false, _ -> Empty
      | true, true -> Maybe)
    (index analysis path)

let list_inside analysis path =
  match index analysis path with
  | None -> []
  | Some position ->
      List.filter_map
        (fun inner -> if inner = position then None else Some analysis.paths.(inner))
        analysis.inside.(position)

let list_children analysis position =
  let descendants = List.filter (fun inner -> inner <> position) analysis.inside.(position) in
  List.filter
    (fun inner ->
      not
        (List.exists
           (fun other ->
             other <> inner && is_inside ~outer:analysis.paths.(other) analysis.paths.(inner))
           descendants))
    descendants

let rec mark_needed_flags analysis state position =
  if state.maybe_holds.(position) then begin
    if state.maybe_empty.(position) && not (List.mem position analysis.flagged) then
      analysis.flagged <- position :: analysis.flagged;
    List.iter (mark_needed_flags analysis state) (list_children analysis position)
  end

let list_flagged analysis = List.map (fun position -> analysis.paths.(position)) analysis.flagged

let list_changed analysis ~before ~after =
  List.filter_map
    (fun position ->
      if
        before.maybe_holds.(position) <> after.maybe_holds.(position)
        || before.maybe_empty.(position) <> after.maybe_empty.(position)
      then Some (analysis.paths.(position), after.maybe_holds.(position))
      else None)
    analysis.flagged

let list_held_at_entry analysis =
  List.filter_map
    (fun position ->
      let path = analysis.paths.(position) in
      if List.mem path.local analysis.parameters then Some path else None)
    analysis.flagged

let copy_entry_state analysis block = copy analysis.entries.(block)

let list_given_on_entry analysis block =
  List.concat_map
    (fun local ->
      List.filter_map
        (fun position ->
          if List.mem position analysis.flagged then Some analysis.paths.(position) else None)
        (list_affected_by_local analysis local))
    (Option.value (Hashtbl.find_opt analysis.loop_parts block) ~default:[])

let flow_into analysis state (terminator : Mir.Graph.terminator) successor =
  match terminator with
  | For { iteration = Pull _; part; body; _ } when successor = body ->
      let state = copy state in
      set_holds state (list_affected_by_local analysis part);
      state
  | Resume { exits; _ } -> (
      match List.find_opt (fun (exit : Mir.Graph.early_exit) -> exit.resume = successor) exits with
      | Some { returned = Some local; _ } ->
          let state = copy state in
          set_holds state (list_affected_by_local analysis local);
          state
      | Some { returned = None; _ } | None -> state)
  | For _ | Goto _ | Branch _ | Fork _ | Join _ | Iteration_end _ | Yield _ | Return _ | Cancel _
  | Unreachable | Written_unreachable | Todo ->
      state

let make_owner_test ?(passed = fun _ -> None) (body : Mir.Graph.body) =
  let parts =
    Array.fold_left
      (fun parts (block : Mir.Graph.basic_block) ->
        match block.terminator with
        | For { iteration = Pull _ | Range _; part; _ } -> part :: parts
        | _ -> parts)
      [] body.blocks
  in
  let owns local =
    (not (List.mem local body.captures))
    &&
    match (passed local, body.locals.(local).kind) with
    | Some mode, _ -> mode = Types.Own
    | None, (Temporary | Source { mode = Own; _ }) -> true
    | None, (Source { mode = Read | Mut; _ } | Lent _) -> false
  in
  let lent_mut local =
    (not (owns local))
    && (not (List.mem local parts))
    && (not (List.mem local body.captures))
    &&
    match (passed local, body.locals.(local).kind) with
    | Some mode, _ -> mode = Types.Mut
    | None, (Source { mode = Mut; _ } | Lent Mut) -> true
    | None, (Source { mode = Read | Own; _ } | Lent (Read | Own) | Temporary) -> false
  in
  (owns, lent_mut)

let analyse ?passed ?(moving = fun _ -> true) ~tracks:needs_drop (body : Mir.Graph.body) =
  let owns, lent_mut = make_owner_test ?passed body in
  let tracks local = owns local || lent_mut local in
  let moves = list_moves ~moving and terminator_moves = list_terminator_moves ~moving ~owns in
  let candidates = Place_table.create 64 in
  let add path = Place_table.replace candidates path () in
  let consider (place : Mir.place) =
    match path_of_place place with
    | Some path when tracks path.local ->
        let rec ancestors projections =
          add { path with projections };
          match List.rev projections with [] -> () | _ :: rest -> ancestors (List.rev rest)
        in
        ancestors path.projections
    | _ -> ()
  in
  let consider_local local = consider { root = Local local; projections = [] } in
  List.iter consider_local body.parameters;
  Array.iter
    (fun (basic : Mir.Graph.basic_block) ->
      List.iter
        (fun statement ->
          List.iter (fun (place, _) -> consider place) (moves statement);
          List.iter consider (list_inits statement);
          List.iter consider_local (list_ended statement))
        basic.statements;
      List.iter (fun (place, _) -> consider place) (terminator_moves basic);
      match basic.terminator with
      | For { iteration = Pull _; part; _ } -> consider_local part
      | Resume { exits; _ } ->
          List.iter
            (fun (exit : Mir.Graph.early_exit) -> Option.iter consider_local exit.returned)
            exits
      | For { iteration = Range _; _ }
      | Goto _ | Branch _ | Fork _ | Join _ | Iteration_end _ | Yield _ | Return _ | Cancel _
      | Unreachable | Written_unreachable | Todo ->
          ())
    body.blocks;
  let paths =
    Array.of_list
      (List.sort compare
         (List.filter needs_drop (List.of_seq (Place_table.to_seq_keys candidates))))
  in
  let positions = Place_table.create (Array.length paths) and of_local = Hashtbl.create 16 in
  Array.iteri
    (fun position path ->
      Place_table.replace positions path position;
      Hashtbl.replace of_local path.local
        (position :: Option.value (Hashtbl.find_opt of_local path.local) ~default:[]))
    paths;
  let inside =
    Array.map
      (fun outer ->
        List.filter
          (fun position -> is_inside ~outer paths.(position))
          (Option.value (Hashtbl.find_opt of_local outer.local) ~default:[]))
      paths
  in
  let count = Array.length paths in
  let empty () =
    {
      maybe_holds = Array.make count false;
      maybe_empty = Array.make count false;
      moved_at = Array.make count [];
    }
  in
  let parameters = List.filter tracks body.parameters in
  let analysis =
    {
      paths;
      positions;
      of_local;
      inside;
      parameters;
      is_owner = owns;
      is_lent = lent_mut;
      is_moving = moving;
      loop_parts =
        (let parts = Hashtbl.create 4 in
         Array.iter
           (fun (basic : Mir.Graph.basic_block) ->
             match basic.terminator with
             | For { iteration = Pull _; part; body; _ } -> Hashtbl.add parts body part
             | _ -> ())
           body.blocks;
         let gathered = Hashtbl.create 4 in
         Hashtbl.iter
           (fun block _ -> Hashtbl.replace gathered block (Hashtbl.find_all parts block))
           parts;
         gathered);
      entries = Array.init (Array.length body.blocks) (fun _ -> empty ());
      flagged = [];
    }
  in
  if Array.length body.blocks > 0 then begin
    let start = analysis.entries.(0) in
    Array.iteri
      (fun position path ->
        let holds = List.mem path.local parameters in
        start.maybe_holds.(position) <- holds;
        start.maybe_empty.(position) <- not holds)
      paths
  end;
  let reached = Array.make (Array.length body.blocks) false in
  if Array.length body.blocks > 0 then reached.(0) <- true;
  let join into state =
    let changed = ref false in
    for position = 0 to count - 1 do
      if state.maybe_holds.(position) && not into.maybe_holds.(position) then begin
        into.maybe_holds.(position) <- true;
        changed := true
      end;
      if state.maybe_empty.(position) && not into.maybe_empty.(position) then begin
        into.maybe_empty.(position) <- true;
        changed := true
      end;
      let added =
        List.filter
          (fun origin -> not (List.mem origin into.moved_at.(position)))
          state.moved_at.(position)
      in
      if added <> [] then begin
        into.moved_at.(position) <- into.moved_at.(position) @ added;
        changed := true
      end
    done;
    !changed
  in
  let changed = ref true in
  while !changed do
    changed := false;
    Array.iteri
      (fun block (basic : Mir.Graph.basic_block) ->
        if reached.(block) then begin
          let state = copy analysis.entries.(block) in
          List.iter (apply analysis state) basic.statements;
          apply_effects analysis state ~moves:(terminator_moves basic) ~inits:[] ~ends:[];
          List.iter
            (fun successor ->
              let state =
                match Mir.Graph.find_iteration_loop basic.terminator with
                | Some loop -> flow_into analysis state body.blocks.(loop).terminator successor
                | None -> flow_into analysis state basic.terminator successor
              in
              if not reached.(successor) then begin
                reached.(successor) <- true;
                analysis.entries.(successor) <- copy state;
                changed := true
              end
              else if join analysis.entries.(successor) state then changed := true)
            (Mir.Graph.list_block_successors body block)
        end)
      body.blocks
  done;
  Array.iteri
    (fun block (basic : Mir.Graph.basic_block) ->
      if reached.(block) then begin
        let state = copy analysis.entries.(block) in
        let drop_local local =
          if owns local then
            List.iter
              (fun position ->
                if analysis.paths.(position).projections = [] then
                  mark_needed_flags analysis state position)
              (list_affected_by_local analysis local)
        in
        List.iter
          (fun statement ->
            List.iter
              (fun (place, origin) -> set_empty ~origin state (list_affected analysis place))
              (moves statement);
            List.iter
              (fun place ->
                Option.iter
                  (fun path -> Option.iter (mark_needed_flags analysis state) (index analysis path))
                  (path_of_place place))
              (list_inits statement);
            List.iter drop_local (list_ended statement);
            apply_effects analysis state ~moves:[] ~inits:(list_inits statement)
              ~ends:(list_ended statement))
          basic.statements;
        List.iter
          (fun (place, origin) -> set_empty ~origin state (list_affected analysis place))
          (terminator_moves basic);
        match basic.terminator with
        | Return _ -> List.iter drop_local parameters
        | Yield _ ->
            Array.iteri
              (fun position path ->
                if path.projections = [] && owns path.local then
                  mark_needed_flags analysis state position)
              analysis.paths
        | Goto _ | Branch _ | For _ | Fork _ | Join _ | Iteration_end _ | Cancel _ | Resume _
        | Unreachable | Written_unreachable | Todo ->
            ()
      end)
    body.blocks;
  analysis.flagged <- List.sort_uniq compare analysis.flagged;
  analysis

let list_place_locals (place : Mir.place) =
  match place.root with Local local -> [ local ] | Constant _ | Literal _ -> []

let use_locals uses = List.concat_map (fun use -> list_place_locals use.place) uses
let accept_all _ = true

let list_reads_and_writes (statement : Mir.Graph.statement) =
  match statement.kind with
  | Live locals -> ([], locals)
  | _ ->
      let given = list_inits statement in
      ( use_locals (uses ~moving:accept_all statement)
        @ List.concat_map
            (fun (place : Mir.place) ->
              if place.projections = [] then [] else list_place_locals place)
            given,
        List.filter_map
          (fun (place : Mir.place) ->
            match place with { root = Local local; projections = [] } -> Some local | _ -> None)
          given )

let compute_live_after analysis (body : Mir.Graph.body) =
  let count = Array.length body.locals in
  let sources = Array.make count [] in
  let bind local others = sources.(local) <- others @ sources.(local) in
  Array.iter
    (fun (basic : Mir.Graph.basic_block) ->
      List.iter
        (fun (statement : Mir.Graph.statement) ->
          match statement.kind with
          | Assign { target = { root = Local local; projections = [] }; value; _ }
            when not (owns analysis local) ->
              bind local
                (use_locals
                   (List.filter
                      (fun use -> match use.operand with Some (Borrow _) -> true | _ -> false)
                      (list_rvalue_uses ~moving:accept_all ~origin:statement.origin value)))
          | Lend { part; call } -> bind part (use_locals (list_call_uses ~moving:accept_all call))
          | _ -> ())
        basic.statements)
    body.blocks;
  let rec with_sources seen = function
    | [] -> seen
    | local :: rest when List.mem local seen -> with_sources seen rest
    | local :: rest -> with_sources (local :: seen) (sources.(local) @ rest)
  in
  let reads locals = with_sources [] locals in
  let effects =
    Array.map
      (fun (basic : Mir.Graph.basic_block) -> List.map list_reads_and_writes basic.statements)
      body.blocks
  in
  let entered = Hashtbl.create 4 in
  Array.iter
    (fun (basic : Mir.Graph.basic_block) ->
      match basic.terminator with
      | For { iteration; part; body = first; _ } ->
          Hashtbl.replace entered first
            ( part,
              match iteration with
              | Pull { cursor; _ } -> reads (list_place_locals cursor)
              | Range _ -> [] )
      | _ -> ())
    body.blocks;
  let before =
    Array.map
      (fun (basic : Mir.Graph.basic_block) ->
        Array.init (List.length basic.statements + 2) (fun _ -> Array.make count false))
      body.blocks
  in
  let entry = Array.map (fun _ -> Array.make count false) body.blocks in
  let changed = ref true in
  while !changed do
    changed := false;
    for block = Array.length body.blocks - 1 downto 0 do
      let basic = body.blocks.(block) in
      let positions = before.(block) and last = List.length basic.statements in
      let current = Array.make count false in
      List.iter
        (fun successor ->
          Array.iteri
            (fun local is_live -> if is_live then current.(local) <- true)
            entry.(successor))
        (Mir.Graph.list_block_successors body block);
      positions.(last + 1) <- Array.copy current;
      List.iter
        (fun local -> current.(local) <- true)
        (reads (use_locals (list_terminator_uses ~moving:accept_all ~owns:analysis.is_owner basic)));
      positions.(last) <- Array.copy current;
      List.iteri
        (fun index (read, writes) ->
          List.iter (fun local -> current.(local) <- false) writes;
          List.iter (fun local -> current.(local) <- true) (reads read);
          positions.(last - 1 - index) <- Array.copy current)
        (List.rev effects.(block));
      Option.iter
        (fun (part, cursor) ->
          current.(part) <- false;
          List.iter (fun local -> current.(local) <- true) cursor)
        (Hashtbl.find_opt entered block);
      if current <> entry.(block) then begin
        entry.(block) <- current;
        changed := true
      end
    done
  done;
  fun block step local -> before.(block).(step + 1).(local)

let list_terminator_uses analysis basic =
  list_terminator_uses ~moving:analysis.is_moving ~owns:analysis.is_owner basic
