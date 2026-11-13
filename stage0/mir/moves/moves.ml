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

(* Effects *)

let by_value : Mir.operand -> Mir.place list = function
  | Use { place; _ } | Take { place; _ } -> [ place ]
  | Borrow _ | Constant _ -> []

let rvalue_moves : Mir.rvalue -> Mir.place list = function
  | Operand operand -> by_value operand
  | Operation { operands; _ } | Array operands -> List.concat_map by_value operands
  | Construct { fields; _ } ->
      List.concat_map (fun (_, field) -> Option.fold ~none:[] ~some:by_value field) fields
  | To_any { value; _ } -> by_value value
  | Compare _ | Not _ | Convert _ | Is_variant _ | Copy _ | Function_value _ | Value_parameter _
  | Lambda _ ->
      []

let argument_moves (call : Mir.call) =
  List.concat_map
    (function
      | Mir.Passed
          { mode = Own; value = Use { place; _ } | Borrow { place; _ } | Take { place; _ }; _ } ->
          [ place ]
      | Passed _ | Default -> [])
    call.arguments

let moves (statement : Mir.statement) =
  match statement.kind with
  | Assign { value; _ } -> rvalue_moves value
  | Call { call; _ } | Lend { call; _ } | Slice { call; _ } | Template { call; _ } ->
      argument_moves call
  | Pull _ | Live _ | Dead _ | Assert _ | Echo _ | Provide _ | Provide_end | Loan_start _
  | Loan_end _ | Ghost_assert _ | Matched _ | Proof _ ->
      []

(* The places a statement gives values. *)
let inits (statement : Mir.statement) : Mir.place list =
  match statement.kind with
  | Assign { target; _ } -> [ target ]
  | Call { destination; _ } -> Option.to_list destination
  | Lend { part; _ } -> [ { root = Local part; projections = [] } ]
  | Slice { destination; _ } | Template { destination; _ } | Pull { destination; _ } ->
      [ destination ]
  | Live _ | Dead _ | Assert _ | Echo _ | Provide _ | Provide_end | Loan_start _ | Loan_end _
  | Ghost_assert _ | Matched _ | Proof _ ->
      []

let ends (statement : Mir.statement) = match statement.kind with Dead locals -> locals | _ -> []

let rec yielded_moves : Mir.yielded -> Mir.place list = function
  | Part operand -> by_value operand
  | Built { fields; _ } ->
      List.concat_map (fun (_, field) -> Option.fold ~none:[] ~some:yielded_moves field) fields

let terminator_moves : Mir.terminator -> Mir.place list = function
  | Return (Some operand) -> by_value operand
  | Exit_tasks { exit = Exit_return (Some operand); _ } -> by_value operand
  | Yield { part; _ } -> yielded_moves part
  | Goto _ | Branch _ | Switch_variant _ | For _ | Fork _ | Join _ | Iteration_end
  | Return None
  | Exit_tasks _ | Unreachable | Written_unreachable | Todo ->
      []

(* The locals a terminator's exit from tasks ends on its way out. *)
let terminator_ends : Mir.terminator -> Mir.local list = function
  | Exit_tasks { tasks; _ } ->
      List.concat_map (fun (left : Mir.left_task) -> List.concat_map ends left.ends) tasks
  | _ -> []

(* The analysis *)

type t = {
  paths : path array;  (** Every tracked path, sorted *)
  positions : (path, int) Hashtbl.t;  (** Each tracked path's place in [paths] *)
  of_local : (Mir.local, int list) Hashtbl.t;  (** The tracked paths of each local *)
  inside : int list array;  (** For each path, the tracked paths within it, itself included *)
  parameters : Mir.local list;
  owner : Mir.local -> bool;
  loop_parts : (Mir.block, Mir.local list) Hashtbl.t;
      (** The parts that the way into each loop's body gives values *)
  entries : state array;  (** The state where each block starts *)
  mutable flagged : int list;
}

and state = { maybe_holds : bool array; maybe_empty : bool array }

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
  { maybe_holds = Array.copy state.maybe_holds; maybe_empty = Array.copy state.maybe_empty }

let set_empty state positions =
  List.iter
    (fun position ->
      state.maybe_holds.(position) <- false;
      state.maybe_empty.(position) <- true)
    positions

let set_holds state positions =
  List.iter
    (fun position ->
      state.maybe_holds.(position) <- true;
      state.maybe_empty.(position) <- false)
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
  List.iter (fun place -> set_empty state (affected analysis place)) moves;
  List.iter
    (fun place ->
      set_holds state (affected analysis place);
      Option.iter (promote analysis state) (path_of_place place))
    inits;
  List.iter (fun local -> set_empty state (affected_local analysis local)) ends

let apply_moves analysis state statement =
  apply_effects analysis state ~moves:(moves statement) ~inits:[] ~ends:[]

let owns analysis local = analysis.owner local

let apply analysis state statement =
  apply_effects analysis state ~moves:(moves statement) ~inits:(inits statement)
    ~ends:(ends statement)

let apply_terminator_moves analysis state terminator =
  apply_effects analysis state ~moves:(terminator_moves terminator) ~inits:[] ~ends:[]

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

(* The tracked paths inside a path that no other tracked path inside it
   holds. *)
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

(* Marks the paths whose drop here needs a flag: one that may or may not
   hold a value, and each part of one that may hold a value that may not,
   since such a part is dropped on its own. *)
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

(* The state a terminator passes to one of its successors: a loop that pulls
   values gives its part one on the way into its body, and an exit from
   tasks ends the scopes it leaves on the way to its target, not where the
   task ends without it. *)
let into analysis state (terminator : Mir.terminator) successor =
  match terminator with
  | For { iteration = Pull _; part; body; _ } when successor = body ->
      let state = copy state in
      set_holds state (affected_local analysis part);
      state
  | Exit_tasks { exit = Exit_to target; _ } when successor = target ->
      let state = copy state in
      List.iter
        (fun local -> set_empty state (affected_local analysis local))
        (terminator_ends terminator);
      state
  | _ -> state

let analyse ~owns ~lent_mut ~needs_drop (body : Mir.body) =
  let tracks local = owns local || lent_mut local in
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
          List.iter consider (moves statement);
          List.iter consider (inits statement);
          List.iter consider_local (ends statement))
        basic.statements;
      List.iter consider (terminator_moves basic.terminator);
      List.iter consider_local (terminator_ends basic.terminator);
      match basic.terminator with
      | For { iteration = Pull _; part; _ } -> consider_local part
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
  let empty () = { maybe_holds = Array.make count false; maybe_empty = Array.make count false } in
  let parameters = List.filter tracks body.parameters in
  let analysis =
    {
      paths;
      positions;
      of_local;
      inside;
      parameters;
      owner = owns;
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
          apply_effects analysis state ~moves:(terminator_moves basic.terminator) ~inits:[] ~ends:[];
          List.iter
            (fun successor ->
              let state = into analysis state basic.terminator successor in
              if not reached.(successor) then begin
                reached.(successor) <- true;
                analysis.entries.(successor) <- copy state;
                changed := true
              end
              else if join analysis.entries.(successor) state then changed := true)
            (Mir.successors basic.terminator)
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
            List.iter (fun place -> set_empty state (affected analysis place)) (moves statement);
            List.iter
              (fun place ->
                Option.iter
                  (fun path -> Option.iter (need_flags analysis state) (index analysis path))
                  (path_of_place place))
              (inits statement);
            List.iter drop_local (ends statement);
            apply_effects analysis state ~moves:[] ~inits:(inits statement) ~ends:(ends statement))
          basic.statements;
        set_empty state (List.concat_map (affected analysis) (terminator_moves basic.terminator));
        List.iter drop_local (terminator_ends basic.terminator);
        match basic.terminator with
        | Return _ | Exit_tasks { exit = Exit_return _; _ } -> List.iter drop_local parameters
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
