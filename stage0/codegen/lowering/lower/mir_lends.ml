let lend_record (state : Lowering.state) : Lowered.operand =
  match state.lend_record with
  | Some record -> record
  | None ->
      let record : Lowered.operand =
        Address
          {
            place =
              Lowered.make_local_place
                (Emit_c.Ir_builder.allocate_local state.builder ~is_zeroed:true Lend);
            writable = true;
          }
      in
      state.lend_record <- Some record;
      record

let obtain_lent_call state part : Lowering.lent_call =
  let frame = Mir_places.require_mir_frame state in
  match Hashtbl.find_opt frame.lent_calls part with
  | Some call -> call
  | None ->
      let call =
        {
          Lowering.mark =
            Lowered.make_local_place
              (Emit_c.Ir_builder.allocate_local state.builder ~is_zeroed:true Lend_mark);
          record = lend_record state;
        }
      in
      Hashtbl.replace frame.lent_calls part call;
      call

let emit_mark (state : Lowering.state) (intrinsic : Lowered.intrinsic) (call : Lowering.lent_call) =
  Emit_c.Ir_builder.emit state.builder
    (Call
       {
         target = Intrinsic intrinsic;
         arguments = [ call.record; Address { place = call.mark; writable = true } ];
         result = Discarded;
       })

let find_forwarded_call state (call : Mir.call) : Forwarded.t option =
  match Mir_calls.resolve_callee state call.callee with
  | Some (path, instantiation) when Path.locate_package path = Path.standard_package ->
      let frame = Mir_places.require_mir_frame state in
      let code = Definitions.make_code state.context path instantiation in
      let passes_no_evidence (forwarded_call : Mir.call) =
        Definitions.list_evidence state.context code.substitution forwarded_call.callee.uses = []
      in
      Option.bind
        (Forwarded.forward_call ~substitution:code.substitution
           ~make_fresh_local:frame.make_forwarded_local
           (Mir_places.read_mir_graph state.context path)
           call)
        (fun (forwarded : Forwarded.t) ->
          if
            (match forwarded.lent with Call call -> passes_no_evidence call | Place _ -> true)
            && List.for_all
                 (fun (_, type_, setup_call) ->
                   Lowering.is_trivial state (Lowering.ground state type_)
                   && passes_no_evidence setup_call)
                 forwarded.setup
          then Some forwarded
          else None)
  | _ -> None

let is_forwarded_whole (frame : Lowering.mir_frame) part =
  match frame.body.blocks.((frame.block :> int)).terminator with
  | Yield { part = Part (Borrow { place = { root = Local lent; projections = [] }; _ }); _ } ->
      lent = part
  | _ -> false

let make_owned_locals state =
  let frame = Mir_places.require_mir_frame state in
  let parts =
    Array.fold_left
      (fun parts (block : Mir.Graph.basic_block) ->
        match block.terminator with For { part; _ } -> part :: parts | _ -> parts)
      [] frame.body.blocks
  in
  Mir.iteri_locals
    (fun local _ ->
      if
        Moves.owns frame.moves local
        && (not (List.mem local frame.body.parameters))
        && not (List.mem local parts)
      then ignore (Mir_places.lookup_local_place state local))
    frame.body.locals

let outlives_call ~(owns : Mir.local -> bool) ~(is_view : Types.ty -> bool) (body : Mir.Graph.body)
    (place : Mir.place) : bool =
  let find_operand_place (operand : Mir.operand) =
    match operand with
    | Borrow { place; type_; _ } | Use { place; type_; _ } | Take { place; type_; _ } ->
        Some (place, is_view type_)
    | Immediate _ -> None
  in
  let list_viewed_by (call : Mir.call) =
    List.filter_map
      (function
        | Mir.Passed { mode; value; _ } -> (
            match find_operand_place value with
            | Some (place, holds_view) when holds_view || mode <> Own -> Some (place, holds_view)
            | _ -> None)
        | Default -> None)
      call.arguments
  in
  let list_receiver_places (call : Mir.call) =
    match call.arguments with
    | Passed { mode = Read | Mut; value; _ } :: _ -> Option.to_list (find_operand_place value)
    | _ -> []
  in
  let find_sources ~holds_view local : (Mir.place * bool) list option =
    let exception Made in
    let is_local (target : Mir.place) = target = { root = Local local; projections = [] } in
    let list_passed_places (statement : Mir.Graph.statement) =
      match statement.kind with
      | Basic (Assign { target; value; _ }) when is_local target -> (
          match value with
          | Operand (Borrow { place; _ }) -> [ (place, holds_view) ]
          | Operand ((Use _ | Take _) as operand) when holds_view ->
              Option.to_list (find_operand_place operand)
          | Construct { fields; _ } when holds_view ->
              List.filter_map
                (fun (_, field) ->
                  match (field : Mir.operand option) with
                  | Some (Borrow { place; _ }) -> Some (place, false)
                  | Some operand ->
                      Option.bind (find_operand_place operand) (fun (place, holds_view) ->
                          if holds_view then Some (place, true) else None)
                  | None -> None)
                fields
          | _ -> raise Made)
      | Basic (Lend { part; call }) when part = local ->
          if holds_view then list_receiver_places call @ list_viewed_by call
          else list_receiver_places call
      | Basic (Call { destination = Some target; call } | Template { destination = target; call; _ })
        when is_local target ->
          if holds_view then list_viewed_by call else raise Made
      | Basic
          ( Assign _ | Lend _ | Call _ | Template _ | Live _ | Dead _ | Assert _ | Echo _
          | Loan_start _ | Loan_end _ | Ghost_assert _ | Path_note _ | Proof _ )
      | Provide_start _ | Provide_end ->
          []
    in
    try
      Some
        (Array.fold_left
           (fun places (block : Mir.Graph.basic_block) ->
             let places =
               List.fold_left
                 (fun places statement -> list_passed_places statement @ places)
                 places block.statements
             in
             match block.terminator with
             | For { iteration = Pull { cursor; _ }; part; _ } when part = local && holds_view ->
                 (cursor, true) :: places
             | For { part; _ } when part = local -> raise Made
             | Resume { exits; _ }
               when List.exists
                      (fun (exit : Mir.Graph.early_exit) -> exit.returned = Some local)
                      exits ->
                 raise Made
             | Cancel { winner; returned; _ }
               when winner = local || Option.map snd returned = Some local ->
                 raise Made
             | For _ | Resume _ | Cancel _ | Goto _ | Branch _ | Fork _ | Join _ | Iteration_end _
             | Yield _ | Return _ | Unreachable | Written_unreachable | Todo ->
                 places)
           [] body.blocks)
    with Made -> None
  in
  let rec outlives seen ~holds_view (place : Mir.place) =
    match place.root with
    | Constant _ | Literal _ -> true
    | Local local when List.mem (local, holds_view) seen -> true
    | Local local -> (
        match body.locals.((local :> int)).kind with
        | Source { mode = Read | Mut; _ } when List.mem local body.parameters -> true
        | _ when List.mem local body.parameters -> holds_view
        | _ when owns local && not holds_view -> false
        | _ -> (
            match find_sources ~holds_view local with
            | Some places ->
                List.for_all
                  (fun (place, holds_view) ->
                    outlives ((local, holds_view) :: seen) ~holds_view place)
                  places
            | None -> false))
  in
  outlives [] ~holds_view:false place
