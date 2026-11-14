type step = Field of string | Variant of { variant : string; field : string }
type path = { local : Mir.local; steps : step list }

let path_of_place (place : Mir.place) =
  match place.root with
  | Constant _ -> None
  | Local local ->
      Some
        {
          local;
          steps =
            List.map
              (function
                | Mir.Field field -> Field field
                | Variant_field { variant; field } -> Variant { variant; field })
              place.projections;
        }

let rec is_prefix prefix steps =
  match (prefix, steps) with
  | [], _ -> true
  | step :: prefix, other :: steps -> step = other && is_prefix prefix steps
  | _ :: _, [] -> false

(* [inner] is [outer] or lies inside it. *)
let is_inside ~outer inner = outer.local = inner.local && is_prefix outer.steps inner.steps

(* Whether two paths overlap: one is the other or lies inside it. *)
let overlaps first second = is_inside ~outer:first second || is_inside ~outer:second first

(* Effects *)

(* A place a statement or a terminator reads, in evaluation order: where,
   whether the read moves the value out, the operand that reads it, if one
   does, and the mode of the parameter it is passed to, for an argument. *)
type use = {
  place : Mir.place;
  origin : Core.origin;
  moves : bool;
  operand : Mir.operand option;
  passed : Types.mode option;
}

(* A value read by value moves where its type moves, as [moving] says:
   the rest copy implicitly. A place lent for an operation moves nothing;
   one lent to an [own] parameter moves. *)
let operand_use ?passed ~moving ~by_value (operand : Mir.operand) =
  match operand with
  | Use { place; type_; origin; _ } | Take { place; type_; origin } ->
      [ { place; origin; moves = by_value && moving type_; operand = Some operand; passed } ]
  | Borrow { place; type_; origin; _ } ->
      let moves = by_value && Option.is_some passed && moving type_ in
      [ { place; origin; moves; operand = Some operand; passed } ]
  | Constant _ -> []

let read ~origin place = { place; origin; moves = false; operand = None; passed = None }

let rvalue_uses ~moving ~origin (rvalue : Mir.rvalue) =
  let by_value = List.concat_map (operand_use ~moving ~by_value:true)
  and reads = List.concat_map (operand_use ~moving ~by_value:false) in
  match rvalue with
  | Operand operand | To_any { value = operand; _ } -> by_value [ operand ]
  | Operation { operands; _ } | Array operands -> by_value operands
  | Construct { fields; _ } -> by_value (List.filter_map snd fields)
  | Compare { left; right; _ } -> reads [ left; right ]
  | Not operand | Convert { value = operand; _ } | Copy operand -> reads [ operand ]
  | Is_variant { place; _ } -> [ read ~origin place ]
  | Lambda { captures; _ } ->
      List.map (fun (capture : Mir.capture) -> read ~origin capture.place) captures
  | Function_value _ | Value_parameter _ -> []

(* A call moves each argument passed to an [own] parameter whose type
   moves. *)
let call_uses ~moving (call : Mir.call) =
  (match call.callee with
    | Indirect operand -> operand_use ~moving ~by_value:false operand
    | _ -> [])
  @ List.concat_map
      (function
        | Mir.Passed { mode; value; _ } ->
            operand_use ~passed:mode ~moving ~by_value:(mode = Own) value
        | Default -> [])
      call.arguments

let uses ~moving (statement : Mir.statement) =
  let origin = statement.origin in
  match statement.kind with
  | Assign { value; _ } -> rvalue_uses ~moving ~origin value
  | Call { call; _ } | Lend { call; _ } | Template { call; _ } -> call_uses ~moving call
  | Slice { base; call; _ } -> read ~origin base :: call_uses ~moving call
  | Assert { condition = operand; _ } | Echo operand -> operand_use ~moving ~by_value:false operand
  | Provide { provided; _ } ->
      List.concat_map
        (fun (provided : Mir.provided) -> operand_use ~moving ~by_value:false provided.value)
        provided
  | Live _ | Dead _ | Provide_end | Loan_start _ | Loan_end _ | Ghost_assert _ | Matched _ | Proof _
    ->
      []

(* A lending method moves a whole value that it owns to its caller, which
   drops the value when the lend ends. A place of another owner's stays
   where it is. *)
let rec yielded_uses ~moving ~owns : Mir.yielded -> use list = function
  | Part
      (Borrow { place = { root = Local local; projections = [] } as place; type_; origin; _ } as
       operand)
    when owns local ->
      [ { place; origin; moves = moving type_; operand = Some operand; passed = None } ]
  | Part operand -> operand_use ~moving ~by_value:true operand
  | Built { fields; _ } ->
      List.concat_map
        (fun (_, field) -> Option.fold ~none:[] ~some:(yielded_uses ~moving ~owns) field)
        fields

let terminator_uses ~moving ~owns (basic : Mir.basic_block) =
  let origin = basic.terminator_origin in
  match basic.terminator with
  | Branch { condition; _ } -> operand_use ~moving ~by_value:false condition
  | Switch_variant { place; _ } -> [ read ~origin place ]
  | For { iteration = Range { start; stop; _ }; _ } ->
      List.concat_map (operand_use ~moving ~by_value:false) [ start; stop ]
  | For { iteration = Pull { cursor; _ }; _ } -> [ read ~origin cursor ]
  | Yield { part; _ } -> yielded_uses ~moving ~owns part
  | Return (Some operand) | Cancel { returned = Some (operand, _); _ } ->
      operand_use ~moving ~by_value:true operand
  | Resume { winner; _ } -> [ read ~origin { root = Local winner; projections = [] } ]
  | Goto _ | Fork _ | Join _ | Iteration_end _
  | Return None
  | Cancel { returned = None; _ }
  | Unreachable | Written_unreachable | Todo ->
      []

let moved uses =
  List.filter_map (fun use -> if use.moves then Some (use.place, use.origin) else None) uses

let moves ~moving statement = moved (uses ~moving statement)

(* The places a statement gives values. *)
let inits (statement : Mir.statement) : Mir.place list =
  match statement.kind with
  | Assign { target; _ } -> [ target ]
  | Call { destination; _ } -> Option.to_list destination
  | Lend { part; _ } -> [ { root = Local part; projections = [] } ]
  | Slice { destination; _ } | Template { destination; _ } -> [ destination ]
  | Live _ | Dead _ | Assert _ | Echo _ | Provide _ | Provide_end | Loan_start _ | Loan_end _
  | Ghost_assert _ | Matched _ | Proof _ ->
      []

let ends (statement : Mir.statement) = match statement.kind with Dead locals -> locals | _ -> []
let terminator_moves ~moving ~owns basic = moved (terminator_uses ~moving ~owns basic)

(* The analysis *)

type t = {
  paths : path array;  (** Every tracked path, sorted *)
  positions : (path, int) Hashtbl.t;  (** Each tracked path's place in [paths] *)
  of_local : (Mir.local, int list) Hashtbl.t;  (** The tracked paths of each local *)
  inside : int list array;  (** For each path, the tracked paths within it, itself included *)
  parameters : Mir.local list;
  owner : Mir.local -> bool;
  lent : Mir.local -> bool;  (** Whether a local is another owner's place lent [mut] *)
  moving : Types.ty -> bool;
  aliases : (Mir.local, int) Hashtbl.t;  (** How many assignments give each local a place *)
  loop_parts : (Mir.block, Mir.local list) Hashtbl.t;
  entries : state array;  (** The state where each block starts *)
  mutable flagged : int list;
}

and state = {
  maybe_holds : bool array;
  maybe_empty : bool array;
  moved_at : Core.origin list array;
      (** For each path, where the moves that may have left it empty are *)
}

type status = Holds | Empty | Maybe

let index analysis path = Hashtbl.find_opt analysis.positions path

let affected analysis place =
  match path_of_place place with
  | None -> []
  | Some outer ->
      List.filter
        (fun position -> is_inside ~outer analysis.paths.(position))
        (Option.value (Hashtbl.find_opt analysis.of_local outer.local) ~default:[])

let affected_local analysis local = affected analysis { root = Local local; projections = [] }

let copy state =
  {
    maybe_holds = Array.copy state.maybe_holds;
    maybe_empty = Array.copy state.maybe_empty;
    moved_at = Array.copy state.moved_at;
  }

(* Empties paths: by a move at [origin], or where their local ends. *)
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

(* A record holds a value once each of its tracked parts does, however it
   was given them: fields may be given values one by one. *)
let rec promote analysis state path =
  match List.rev path.steps with
  | Field _ :: rest -> (
      let parent = { path with steps = List.rev rest } in
      match index analysis parent with
      | Some parent_position when state.maybe_empty.(parent_position) ->
          let parts =
            List.filter
              (fun position -> position <> parent_position)
              analysis.inside.(parent_position)
          in
          let direct =
            List.filter
              (fun position ->
                match List.rev analysis.paths.(position).steps with
                | Field _ :: rest -> List.rev rest = parent.steps
                | _ -> false)
              parts
          in
          if
            direct <> []
            && List.for_all
                 (fun position -> state.maybe_holds.(position) && not state.maybe_empty.(position))
                 direct
          then begin
            set_holds state [ parent_position ];
            promote analysis state parent
          end
      | _ -> ())
  | _ -> ()

let apply_effects analysis state ~moves ~inits ~ends =
  List.iter (fun (place, origin) -> set_empty ~origin state (affected analysis place)) moves;
  List.iter
    (fun place ->
      set_holds state (affected analysis place);
      Option.iter (promote analysis state) (path_of_place place))
    inits;
  List.iter (fun local -> set_empty state (affected_local analysis local)) ends

let apply_moves analysis state statement =
  apply_effects analysis state ~moves:(moves ~moving:analysis.moving statement) ~inits:[] ~ends:[]

let owns analysis local = analysis.owner local
let lent_mut analysis local = analysis.lent local
let places_given analysis local = Option.value ~default:0 (Hashtbl.find_opt analysis.aliases local)
let statement_uses analysis statement = uses ~moving:analysis.moving statement
let move_out analysis state place ~origin = set_empty ~origin state (affected analysis place)

(* Where the moves are that may have left a path empty. *)
let moved_at analysis state path =
  match index analysis path with Some position -> state.moved_at.(position) | None -> []

let given_by statement = List.filter_map path_of_place (inits statement)
let ended_by = ends

(* The outermost tracked path that overlaps [path], around it or inside it,
   and may hold nothing in [state]. *)
let may_be_empty analysis state (path : path) =
  List.find_opt
    (fun (tracked : path) ->
      overlaps tracked path && state.maybe_empty.(Hashtbl.find analysis.positions tracked))
    (List.sort
       (fun (left : path) (right : path) ->
         compare (List.length left.steps) (List.length right.steps))
       (List.map
          (fun position -> analysis.paths.(position))
          (Option.value (Hashtbl.find_opt analysis.of_local path.local) ~default:[])))

let apply analysis state statement =
  apply_effects analysis state
    ~moves:(moves ~moving:analysis.moving statement)
    ~inits:(inits statement) ~ends:(ends statement)

let apply_terminator_moves analysis state basic =
  apply_effects analysis state
    ~moves:(terminator_moves ~moving:analysis.moving ~owns:analysis.owner basic)
    ~inits:[] ~ends:[]

let status analysis state path =
  Option.map
    (fun position ->
      match (state.maybe_holds.(position), state.maybe_empty.(position)) with
      | true, false -> Holds
      | false, _ -> Empty
      | true, true -> Maybe)
    (index analysis path)

let inside analysis path =
  match index analysis path with
  | None -> []
  | Some position ->
      List.filter_map
        (fun inner -> if inner = position then None else Some analysis.paths.(inner))
        analysis.inside.(position)

let children analysis position =
  let within = List.filter (fun inner -> inner <> position) analysis.inside.(position) in
  List.filter
    (fun inner ->
      not
        (List.exists
           (fun other ->
             other <> inner && is_inside ~outer:analysis.paths.(other) analysis.paths.(inner))
           within))
    within

let rec need_flags analysis state position =
  if state.maybe_holds.(position) then begin
    if state.maybe_empty.(position) && not (List.mem position analysis.flagged) then
      analysis.flagged <- position :: analysis.flagged;
    List.iter (need_flags analysis state) (children analysis position)
  end

let flagged analysis = List.map (fun position -> analysis.paths.(position)) analysis.flagged

let changed analysis ~before ~after =
  List.filter_map
    (fun position ->
      if
        before.maybe_holds.(position) <> after.maybe_holds.(position)
        || before.maybe_empty.(position) <> after.maybe_empty.(position)
      then Some (analysis.paths.(position), after.maybe_holds.(position))
      else None)
    analysis.flagged

let held_at_entry analysis =
  List.filter_map
    (fun position ->
      let path = analysis.paths.(position) in
      if List.mem path.local analysis.parameters then Some path else None)
    analysis.flagged

let entry analysis block = copy analysis.entries.(block)

let given_on_entry analysis block =
  List.concat_map
    (fun local ->
      List.filter_map
        (fun position ->
          if List.mem position analysis.flagged then Some analysis.paths.(position) else None)
        (affected_local analysis local))
    (Option.value (Hashtbl.find_opt analysis.loop_parts block) ~default:[])

let into analysis state (terminator : Mir.terminator) successor =
  match terminator with
  | For { iteration = Pull _; part; body; _ } when successor = body ->
      let state = copy state in
      set_holds state (affected_local analysis part);
      state
  | Resume { exits; _ } -> (
      (* The exit that won left the value it returns in its local. *)
      match List.find_opt (fun (exit : Mir.early_exit) -> exit.resume = successor) exits with
      | Some { returned = Some local; _ } ->
          let state = copy state in
          set_holds state (affected_local analysis local);
          state
      | _ -> state)
  | _ -> state

(* Which locals own their values and which are another owner's places
   lent [mut]. A local that an assignment gives a place holds no
   value of its own, nor does a capture, which is the enclosing body's.
   [passed] says how a parameter is passed where its binding does not:
   a lambda's parameters are patterns, and its function type says how each
   is passed. A loop's part and a capture are no owner's place lent here. *)
let owners ?(passed = fun _ -> None) (body : Mir.body) =
  (* How many assignments give each local a place. *)
  let aliases = Hashtbl.create 8 in
  Array.iter
    (fun (block : Mir.basic_block) ->
      List.iter
        (fun (statement : Mir.statement) ->
          match statement.kind with
          | Assign
              { target = { root = Local local; projections = [] }; value = Operand (Borrow _); _ }
            ->
              Hashtbl.replace aliases local
                (1 + Option.value ~default:0 (Hashtbl.find_opt aliases local))
          | _ -> ())
        block.statements)
    body.blocks;
  let parts =
    Array.fold_left
      (fun parts (block : Mir.basic_block) ->
        match block.terminator with
        | For { iteration = Pull _ | Range _; part; _ } -> part :: parts
        | _ -> parts)
      [] body.blocks
  in
  let owns local =
    (not (Hashtbl.mem aliases local))
    && (not (List.mem local body.captures))
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
  (owns, lent_mut, aliases)

let analyse ?passed ?(moving = fun _ -> true) ~tracks:needs_drop (body : Mir.body) =
  let owns, lent_mut, aliases = owners ?passed body in
  let tracks local = owns local || lent_mut local in
  let moves = moves ~moving and terminator_moves = terminator_moves ~moving ~owns in
  let candidates = Hashtbl.create 64 in
  let add path = Hashtbl.replace candidates path () in
  let consider (place : Mir.place) =
    match path_of_place place with
    | Some path when tracks path.local ->
        let rec ancestors steps =
          add { path with steps };
          match List.rev steps with [] -> () | _ :: rest -> ancestors (List.rev rest)
        in
        ancestors path.steps
    | _ -> ()
  in
  let consider_local local = consider { root = Local local; projections = [] } in
  List.iter consider_local body.parameters;
  Array.iter
    (fun (basic : Mir.basic_block) ->
      List.iter
        (fun statement ->
          List.iter (fun (place, _) -> consider place) (moves statement);
          List.iter consider (inits statement);
          List.iter consider_local (ends statement))
        basic.statements;
      List.iter (fun (place, _) -> consider place) (terminator_moves basic);
      match basic.terminator with
      | For { iteration = Pull _; part; _ } -> consider_local part
      | Resume { exits; _ } ->
          List.iter (fun (exit : Mir.early_exit) -> Option.iter consider_local exit.returned) exits
      | _ -> ())
    body.blocks;
  let paths =
    Array.of_list
      (List.sort compare (List.filter needs_drop (List.of_seq (Hashtbl.to_seq_keys candidates))))
  in
  let positions = Hashtbl.create (Array.length paths) and of_local = Hashtbl.create 16 in
  Array.iteri
    (fun position path ->
      Hashtbl.replace positions path position;
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
      owner = owns;
      lent = lent_mut;
      moving;
      aliases;
      loop_parts =
        (let parts = Hashtbl.create 4 in
         Array.iter
           (fun (basic : Mir.basic_block) ->
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
  (* On entry, the parameters hold values and everything else nothing. *)
  if Array.length body.blocks > 0 then begin
    let start = analysis.entries.(0) in
    Array.iteri
      (fun position path ->
        let holds = List.mem path.local parameters in
        start.maybe_holds.(position) <- holds;
        start.maybe_empty.(position) <- not holds)
      paths
  end;
  (* The end of an iteration flows to the loop's next iteration and to the
     block after the loop. The loop's operands are evaluated once, before
     its first iteration. *)
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
      (fun block (basic : Mir.basic_block) ->
        if reached.(block) then begin
          let state = copy analysis.entries.(block) in
          List.iter (apply analysis state) basic.statements;
          apply_effects analysis state ~moves:(terminator_moves basic) ~inits:[] ~ends:[];
          List.iter
            (fun successor ->
              let state =
                match Mir.iteration_loop basic.terminator with
                | Some loop -> into analysis state body.blocks.(loop).terminator successor
                | None -> into analysis state basic.terminator successor
              in
              if not reached.(successor) then begin
                reached.(successor) <- true;
                analysis.entries.(successor) <- copy state;
                changed := true
              end
              else if join analysis.entries.(successor) state then changed := true)
            (Mir.block_successors body block)
        end)
      body.blocks
  done;
  (* Each place a path is dropped: where its local ends, where it is given a
     value over one it may hold, and, for a parameter, where the function
     returns. *)
  Array.iteri
    (fun block (basic : Mir.basic_block) ->
      if reached.(block) then begin
        let state = copy analysis.entries.(block) in
        let drop_local local =
          if owns local then
            List.iter
              (fun position ->
                if analysis.paths.(position).steps = [] then need_flags analysis state position)
              (affected_local analysis local)
        in
        List.iter
          (fun statement ->
            List.iter
              (fun (place, origin) -> set_empty ~origin state (affected analysis place))
              (moves statement);
            List.iter
              (fun place ->
                Option.iter
                  (fun path -> Option.iter (need_flags analysis state) (index analysis path))
                  (path_of_place place))
              (inits statement);
            List.iter drop_local (ends statement);
            apply_effects analysis state ~moves:[] ~inits:(inits statement) ~ends:(ends statement))
          basic.statements;
        List.iter
          (fun (place, origin) -> set_empty ~origin state (affected analysis place))
          (terminator_moves basic);
        match basic.terminator with
        | Return _ -> List.iter drop_local parameters
        | Yield _ ->
            Array.iteri
              (fun position path ->
                if path.steps = [] && owns path.local then need_flags analysis state position)
              analysis.paths
        | _ -> ()
      end)
    body.blocks;
  analysis.flagged <- List.sort_uniq compare analysis.flagged;
  analysis

(* The locals a cursor keeps *)

let place_locals (place : Mir.place) =
  match place.root with Local local -> [ local ] | Constant _ -> []

let use_locals uses = List.concat_map (fun use -> place_locals use.place) uses
let every _ = true

(* The locals a statement reads and those it gives a whole value, in
   [state], where it runs. A write to a part of a local reads the rest of
   it. Where [drops], an end of a local that may hold a value with something
   to drop reads it, since its drop does. *)
let reads_and_writes analysis ~drops state (statement : Mir.statement) =
  match statement.kind with
  | Live locals -> ([], locals)
  | Dead locals ->
      ( List.filter
          (fun local ->
            drops && owns analysis local
            && List.exists
                 (fun position -> state.maybe_holds.(position))
                 (affected_local analysis local))
          locals,
        [] )
  | _ ->
      let given = inits statement in
      ( use_locals (uses ~moving:every statement)
        @ List.concat_map
            (fun (place : Mir.place) -> if place.projections = [] then [] else place_locals place)
            given,
        List.filter_map
          (fun (place : Mir.place) ->
            match place with { root = Local local; projections = [] } -> Some local | _ -> None)
          given )

let live analysis (body : Mir.body) ~drops =
  let count = Array.length body.locals in
  (* The locals whose places a local is bound to, or holds views of: a use
     of the local uses them too. *)
  let sources = Array.make count [] in
  let bind local others = sources.(local) <- others @ sources.(local) in
  Array.iter
    (fun (basic : Mir.basic_block) ->
      List.iter
        (fun (statement : Mir.statement) ->
          match statement.kind with
          | Assign { target = { root = Local local; projections = [] }; value; _ }
            when not (owns analysis local) ->
              bind local
                (use_locals
                   (List.filter
                      (fun use -> match use.operand with Some (Borrow _) -> true | _ -> false)
                      (rvalue_uses ~moving:every ~origin:statement.origin value)))
          | Lend { part; call } -> bind part (use_locals (call_uses ~moving:every call))
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
    Array.mapi
      (fun block (basic : Mir.basic_block) ->
        let state = copy analysis.entries.(block) in
        List.map
          (fun statement ->
            let read_and_written = reads_and_writes analysis ~drops state statement in
            apply analysis state statement;
            read_and_written)
          basic.statements)
      body.blocks
  in
  (* Each iteration of a loop gives its part a value where its body starts,
     and a loop that pulls values reads its cursor there. *)
  let entered = Hashtbl.create 4 in
  Array.iter
    (fun (basic : Mir.basic_block) ->
      match basic.terminator with
      | For { iteration; part; body = first; _ } ->
          Hashtbl.replace entered first
            ( part,
              match iteration with
              | Pull { cursor; _ } -> reads (place_locals cursor)
              | Range _ -> [] )
      | _ -> ())
    body.blocks;
  let before =
    Array.map
      (fun (basic : Mir.basic_block) ->
        Array.init (List.length basic.statements + 2) (fun _ -> Array.make count false))
      body.blocks
  in
  (* The locals live where control enters each block, before a loop's
     iteration gives its part a value. *)
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
        (Mir.block_successors body block);
      positions.(last + 1) <- Array.copy current;
      List.iter
        (fun local -> current.(local) <- true)
        (reads (use_locals (terminator_uses ~moving:every ~owns:analysis.owner basic)));
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
  fun block index local -> before.(block).(index).(local)

let terminator_uses analysis basic =
  terminator_uses ~moving:analysis.moving ~owns:analysis.owner basic
