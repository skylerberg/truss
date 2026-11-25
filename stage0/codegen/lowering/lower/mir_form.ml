type deferred =
  | Deferred_drop of Ground.ty
  | Deferred_write_back of { source : Lowered.place; ty : Ground.ty }
  | Deferred_free of string

type lent_value =
  | Owned of { dropped_as : Ground.ty option }
  | Holds_lent_places of (Lowered.projection list * deferred) list

let make_owned state ty =
  Owned { dropped_as = (if Lowering.is_trivial state ty then None else Some ty) }

let list_deferred = function
  | Owned { dropped_as = Some ty } -> [ ([], Deferred_drop ty) ]
  | Owned { dropped_as = None } -> []
  | Holds_lent_places deferred -> deferred

let provide (state : Lowering.state) (provided : Mir.provided list) ~can_use_tasks ~site =
  let enclosing = state.evidence in
  let implementations =
    List.map
      (fun (implementation : Mir.provided) ->
        let place =
          match implementation.value with
          | Use { place = written; _ } | Borrow { place = written; _ } ->
              Mir_places.lower_place state written
          | value -> Mir_places.lower_operand_place state value
        in
        let pointer =
          if Lowering.is_zero_size state (Lowering.ground state implementation.type_) then
            Lowered.Constant Null
          else Address { place; writable = true }
        in
        ( implementation.mode,
          Targets.lower_provided_evidence state ~implementation:pointer ~site
            (List.map
               (fun (provided : Core.provided) ->
                 (provided.capability, provided.impl, provided.arguments))
               implementation.provides) ))
      provided
  in
  let is_tasks (capability, _) = Path.equal capability (Well_known.make_path Tasks) in
  let tasks =
    if can_use_tasks then
      Option.map snd (List.find_opt is_tasks (List.concat_map snd implementations @ enclosing))
    else None
  in
  let added =
    List.concat_map
      (fun ((mode : Language.Mode.t), evidence) ->
        match tasks with
        | Some tasks when mode = Mut && not (List.exists is_tasks evidence) ->
            Mir_tasks.lock_evidence state ~tasks evidence
        | _ -> evidence)
      implementations
  in
  let frame = Mir_places.require_mir_frame state in
  frame.provides <- enclosing :: frame.provides;
  state.evidence <- added @ enclosing

let rec lower_body (state : Lowering.state) (frame : Lowering.mir_frame) =
  state.frame <- { state.frame with mir = Some frame };
  List.iter
    (fun path ->
      Emit_c.Ir_builder.emit state.builder
        (Assign (List.assoc path frame.flags, Use (Constant (Bool true)))))
    (Moves.list_held_at_entry frame.moves);
  run_region state (Mir_drops.make_region state) ~entry:(0, 0)

and run_region state (region : Mir_drops.region) ~entry:(block, index) =
  let caller = state.frame in
  state.frame <- region.region_frame;
  lower_from state region block index;
  let rec drain () =
    match
      List.fold_left
        (fun first ((block, _, _) as next) ->
          match first with Some (earliest, _, _) when earliest <= block -> first | _ -> Some next)
        None region.pending
    with
    | None -> ()
    | Some (next, lowered, entry) ->
        region.pending <- List.filter (fun (block, _, _) -> block <> next) region.pending;
        Mir_drops.restore state entry;
        Emit_c.Ir_builder.run_in_block state.builder lowered (fun () ->
            lower_from state region next 0;
            Emit_c.Ir_builder.finish state.builder Unreachable);
        drain ()
  in
  drain ();
  state.frame <- caller

and lower_from state (region : Mir_drops.region) block index =
  let basic = (Mir_places.require_mir_frame state).body.blocks.(block) in
  state.frame <- region.region_frame;
  let frame = Mir_places.require_mir_frame state in
  frame.block <- block;
  frame.move_state <- Moves.copy_entry_state frame.moves block;
  if index = 0 then
    List.iter
      (fun path ->
        Emit_c.Ir_builder.emit state.builder
          (Assign (List.assoc path frame.flags, Use (Constant (Bool true)))))
      (Moves.list_given_on_entry frame.moves block);
  List.iteri
    (fun position (statement : Mir.Graph.statement) ->
      if position >= index then
        Emit_c.Ir_builder.with_site state.builder (Mir_places.locate_site state statement.origin)
          (fun () ->
            let before = Moves.copy frame.move_state in
            Moves.apply_moves frame.moves frame.move_state statement;
            Lowering.run_in_statement state (fun () -> lower_statement state statement);
            Moves.apply frame.moves frame.move_state statement;
            Mir_drops.update_flags state ~before)
      else Moves.apply frame.moves frame.move_state statement)
    basic.statements;
  Emit_c.Ir_builder.with_site state.builder (Mir_places.locate_site state basic.terminator_origin)
    (fun () ->
      let before = Moves.copy frame.move_state in
      Moves.apply_terminator_moves frame.moves frame.move_state basic;
      Mir_drops.update_flags state ~before;
      lower_terminator state region basic.terminator ~origin:basic.terminator_origin)

and lower_concurrent_block state (region : Mir_drops.region) ~fork
    ~(branches : Mir.Graph.branch list) ~join =
  let function_type = Mir_tasks.compute_task_function_type state in
  let item = Emit_c.Ir_builder.allocate_local state.builder (Value (Ground.make_builtin UInt64)) in
  Emit_c.Ir_builder.emit state.builder
    (Assign (Lowered.make_local_place item, Use (Lowering.make_int_constant UInt64 Z.zero)));
  Mir_tasks.with_group state (fun group ->
      let functions =
        List.mapi
          (fun index (branch : Mir.Graph.branch) ->
            Mir_tasks.lower_task_body state
              ~id:(Branch { fork; index })
              ~group ~parts:[ item ]
              (fun task ->
                let inner =
                  Mir_drops.make_region state ~enclosing:region ~ending:(fork, task.end_block)
                in
                run_region state inner ~entry:(branch.entry, 0)))
          branches
      in
      List.iter
        (fun code ->
          let function_value =
            Lowered.make_local_place (Emit_c.Ir_builder.allocate_local state.builder function_type)
          in
          Emit_c.Ir_builder.emit state.builder (Assign (function_value, code));
          ignore
            (Mir_tasks.call_tasks_bool state Tasks_spawn
               [ group; function_value; Lowered.make_local_place item ]))
        functions);
  match join with
  | Some join -> Mir_drops.goto state region join
  | None -> Lowering.emit_unreachable_block state

and lower_statement state (statement : Mir.Graph.statement) =
  let origin = statement.origin in
  match statement.kind with
  | Provide_start { provided; can_use_tasks } ->
      provide state provided ~can_use_tasks ~site:(Some (Mir_places.locate_site state origin))
  | Provide_end -> (
      let frame = Mir_places.require_mir_frame state in
      match frame.provides with
      | enclosing :: rest ->
          state.evidence <- enclosing;
          frame.provides <- rest
      | [] -> Definitions.raise_bug "the end of a provide that did not start")
  | Basic basic -> lower_basic state basic ~origin

and lower_basic state (basic : Mir.basic) ~origin =
  match basic with
  | Assign { target; value; _ } -> assign state target value ~origin
  | Call { destination; call } ->
      let destination =
        match destination with
        | Some written ->
            let destination = Mir_places.lower_place state written in
            (match Lowering.find_place_type state destination with
            | Some (Value ty) -> Mir_drops.drop_overwritten state written destination ty
            | _ -> ());
            destination
        | None -> Mir_places.make_discard_place state
      in
      lower_call_into state call destination ~origin
  | Lend { part; call } -> lend state part call ~origin
  | Live _ | Loan_start _ | Loan_end _ | Ghost_assert _ | Path_note _ | Proof _ | Evaluated_assert _
    ->
      ()
  | Dead locals -> List.iter (Mir_drops.end_local state) locals
  | Assert condition ->
      let holds = Mir_places.lower_operand state condition in
      let failed = Emit_c.Ir_builder.allocate_block state.builder
      and after = Emit_c.Ir_builder.allocate_block state.builder in
      Emit_c.Ir_builder.branch state.builder (Holds holds) ~yes:after ~no:failed;
      Emit_c.Ir_builder.start state.builder failed;
      let message =
        "assert "
        ^ Lowering.quote_span state (Mir_places.read_spans state).(Core_walk.locate_origin origin)
      in
      Emit_c.Ir_builder.finish state.builder
        (Fail
           {
             failure = Assertion;
             message = Constant (Bytes message);
             length = Lowered.make_uint64_constant (String.length message);
             site = Mir_places.locate_site state origin;
             reported = None;
             trace = None;
           });
      Emit_c.Ir_builder.start state.builder after
  | Echo echoed ->
      Targets.echo state
        (Mir_places.lower_operand_place state echoed)
        (Mir_places.compute_operand_type state echoed)
        ~site:(Mir_places.locate_site state origin)

and assign state (target : Mir.place) (value : Mir.rvalue) ~origin =
  match (target, value) with
  | { root = Local local; projections = [] }, Operand (Borrow { place = source; mode; _ }) ->
      Mir_places.alias state local (Mir_places.lower_place state source) ~writable:(mode = Mut)
  | _ -> (
      let ty = Mir_places.compute_target_type state target value in
      let types_ty =
        match target with
        | { root = Local local; projections = [] } ->
            Some (Mir_places.lookup_local_info state local).type_
        | _ -> None
      in
      let reads_target =
        match target.root with
        | Local local -> Mir_places.reads value local
        | Constant _ | Literal _ -> false
      in
      let evaluated =
        if reads_target then begin
          let fresh = Lowering.allocate_temporary state ty in
          lower_rvalue_into ?types_ty state value fresh ty ~origin;
          Some fresh
        end
        else None
      in
      let destination = Mir_places.lower_place state target in
      let frame = Mir_places.require_mir_frame state in
      if List.mem target frame.taken then
        frame.taken <- List.filter (fun taken -> taken <> target) frame.taken
      else Mir_drops.drop_overwritten state target destination ty;
      match (evaluated, value, target) with
      | Some fresh, _, _ ->
          Emit_c.Ir_builder.emit state.builder
            (Assign (destination, Use (Lowering.make_owned_operand state fresh ty)))
      | ( None,
          Parameter_default { definition; position; substitution },
          { root = Local local; projections = [] } ) ->
          let default =
            Mir.read_parameter_default_graph state.context.lookups.mir ~definition ~position
          in
          let caller = state.frame in
          state.frame <-
            {
              caller with
              code =
                Definitions.make_default_code state.context caller.code ~source:default.source
                  ~substitution;
              self_place = None;
            };
          let default_frame = inline_mir state default.form destination in
          state.frame <- caller;
          Option.iter
            (fun (inlined : Lowering.mir_frame) ->
              Option.iter
                (fun at_return -> inlined.move_state <- at_return)
                inlined.move_state_at_return;
              if Mir_drops.list_default_temporaries inlined <> [] then begin
                let is_applied =
                  Lowered.make_local_place
                    (Emit_c.Ir_builder.allocate_local state.builder ~is_zeroed:true (Raw Bool))
                in
                Emit_c.Ir_builder.emit state.builder
                  (Assign (is_applied, Use (Constant (Bool true))));
                Hashtbl.replace (Mir_places.require_mir_frame state).applied_defaults local
                  { default_frame; is_applied }
              end)
            default_frame.mir
      | None, _, _ -> lower_rvalue_into ?types_ty state value destination ty ~origin)

and lower_rvalue_into ?types_ty state (rvalue : Mir.rvalue) (destination : Lowered.place) ty ~origin
    =
  let assign built = Emit_c.Ir_builder.emit state.builder (Assign (destination, built)) in
  match rvalue with
  | Operand operand -> Mir_places.write_operand state operand destination
  | Operation { operation; type_arguments; operands } ->
      let type_arguments, value_arguments = Mir_places.split_arguments state type_arguments in
      ignore
        (Intrinsics.lower ~value_arguments
           ?reported:(Mir_places.find_reported_site state)
           ~trace:(Lowering.find_panic_trace state) state.context.env state.builder
           state.context.types (Scalar operation) ~type_arguments
           (List.map
              (fun operand ->
                let operand_ty = Mir_places.compute_operand_type state operand in
                if Storage.find_storage_element operand_ty <> None then
                  Intrinsics.Place (Mir_places.lower_operand_place state operand)
                else Intrinsics.Value (Mir_places.lower_operand state operand))
              operands)
           ~destination:(Some destination)
           ~site:(Mir_places.locate_site state origin))
  | Compare { comparison; left; right } ->
      assign
        (Compare
           ( Mir_places.convert_comparison comparison,
             Mir_places.lower_operand state left,
             Mir_places.lower_operand state right ))
  | Not inner -> assign (Unary (Not, Mir_places.lower_operand state inner))
  | Construct { variant; fields; type_ } ->
      let built = Lowering.ground state type_ in
      let fields =
        List.map
          (fun (name, (field : Mir.operand option)) ->
            match field with
            | Some field -> (name, Mir_places.lower_operand state field)
            | None ->
                let default, default_ty =
                  lower_field_default_place state built ~variant ~field:name
                in
                (name, Lowering.make_owned_operand state default default_ty))
          fields
      in
      assign (Build { ty = built; variant; fields })
  | Array elements ->
      List.iteri
        (fun index element ->
          Mir_places.write_operand state element
            (Lowered.project destination (Index (Lowered.make_uint64_constant index))))
        elements
  | Is_variant { place = tested; variant } ->
      assign (Is_variant (Mir_places.lower_place state tested, variant))
  | Convert { conversion = Widen; value = inner; _ } -> (
      match (Mir_places.compute_operand_type state inner, ty) with
      | Function source, Function target when source <> target ->
          let source_place = Mir_places.lower_operand_place state inner in
          List.iter
            (fun project ->
              Emit_c.Ir_builder.emit state.builder
                (Assign (project destination, Use (Copy (project source_place)))))
            [
              Builtin_records.Function_value.project_code;
              Builtin_records.Function_value.project_environment;
            ]
      | _ -> Mir_places.write_operand state inner destination)
  | Convert { conversion = To_integer | From_integer; _ } ->
      Definitions.raise_bug "a conversion that exists only in specifications"
  | Convert { conversion = To_view; value; _ } ->
      Emit_c.Ir_builder.emit state.builder
        (Assign (destination, Use (Copy (Mir_places.lower_operand_place state value))))
  | Copy source ->
      Drop_and_copy.copy_into state.context.drop_and_copy state.builder ~destination
        ~source:(Mir_places.lower_operand_place state source)
        ty
  | Function_value { path; instantiation; _ } -> (
      match ty with
      | Function function_type ->
          let adapter : Lowered.Item.generated =
            Adapter
              {
                function_ = path;
                instantiation = Mir_calls.ground_instantiation state instantiation;
                ty = function_type;
              }
          in
          assign (Function_value { code = Item (Generated adapter); environment = None })
      | _ -> Definitions.raise_bug "a function value of type %s" (Ground.to_string ty))
  | Value_parameter parameter -> (
      match Mir_places.ground_argument state (Value (Value_parameter parameter)) with
      | Value number -> assign (Use (Targets.lower_literal state ty (Integer_value number)))
      | _ -> Definitions.raise_bug "the value parameter %s is not a number" parameter.name)
  | Parameter_default _ ->
      Definitions.raise_bug "a default assigned to a place that is no temporary of its own"
  | Lambda { body = index; captures; _ } ->
      let function_type =
        match ty with
        | Function function_type -> function_type
        | _ -> Definitions.raise_bug "a lambda of %s" (Ground.to_string ty)
      in
      let lambdas = (Mir_places.require_mir_frame state).lambdas in
      let lambda = lambdas.(index) in
      Targets.lower_nested_function state ~function_type
        ~output:
          (match types_ty with
          | Some (Types.Function function_type) -> Some (Types.Returns function_type.output)
          | _ -> None)
        ~captures:
          (List.map
             (fun (capture : Mir.capture) ->
               (Mir_places.lower_place state capture.place, Lowering.ground state capture.type_))
             captures)
        ~body:(fun inner ~captures:capture_places parameter_places ->
          inner.frame <-
            {
              inner.frame with
              mir =
                Some
                  (Mir_places.make_body_frame inner
                     ~owner:(Lowering.lookup_innermost_scope inner)
                     ~passed:(List.map (fun (_, mode, _) -> mode) parameter_places)
                     ~lambdas lambda);
            };
          List.iter2 (Mir_places.bind_local inner) lambda.captures capture_places;
          Mir_lends.make_owned_locals inner;
          List.iter2
            (fun local (place, _, _) -> Mir_places.bind_local inner local place)
            lambda.parameters parameter_places;
          lower_body inner (Option.get inner.frame.mir))
        destination
  | Specification _ -> Definitions.raise_bug "a specification's expression in code that runs"

and lower_field_default_place state ty ~variant ~field =
  let { Mir.source; form = default } = Mir_calls.read_field_default state ty ~variant ~field in
  Targets.run_in_type_definition state ~source ty (fun () ->
      let default_ty = Lowering.ground state default.type_ in
      let place = Lowering.allocate_temporary state default_ty in
      lower_mir_into state default.value place;
      (place, default_ty))

and inline_mir ?(arguments = []) state (expression_mir : Mir.Graph.t) (destination : Lowered.place)
    : Lowering.frame =
  let expression_mir = Loop_parts.end_parts expression_mir in
  let caller = state.frame in
  let exit = Emit_c.Ir_builder.allocate_block state.builder in
  let frame =
    Mir_places.make_body_frame state ~returns_into:destination ~lambdas:expression_mir.lambdas
      expression_mir.body
  in
  let inlined = { caller with exit = Some (exit, List.length state.scopes); mir = Some frame } in
  state.frame <- inlined;
  List.iter2 (Mir_places.bind_local state) expression_mir.body.parameters arguments;
  lower_body state frame;
  Emit_c.Ir_builder.finish state.builder Unreachable;
  Emit_c.Ir_builder.start state.builder exit;
  state.frame <- caller;
  inlined

and lower_mir_into ?arguments state expression_mir destination =
  ignore (inline_mir ?arguments state expression_mir destination)

and lower_call_into state (call : Mir.call) destination ~origin =
  match call.callee.target with
  | Function _ | Trait_method _ -> (
      let path, instantiation = Mir_calls.resolve_item state call.callee in
      let signature, substitution = Mir_calls.read_callee_signature state path instantiation in
      let arguments = Mir_calls.evaluate_arguments state signature substitution call.arguments in
      match signature.output with
      | Returns _ ->
          Targets.lower_item_call state
            (Lowered.Item.make_code path instantiation)
            ~signature ~substitution ~arguments ~destination
            ~site:(Some (Mir_places.locate_site state origin))
            ()
      | Lends _ -> Definitions.raise_bug "a lending call that lends no part")
  | Intrinsic { operation = Runtime Holds_invariant; _ } -> (
      match call.arguments with
      | [ value; clause ] -> check_invariant state ~value ~clause ~destination
      | _ -> Definitions.raise_bug "holds_invariant takes a value and a clause")
  | Intrinsic { operation; type_arguments } -> (
      match
        Mir_calls.lower_intrinsic state operation ~type_arguments call.arguments
          ~destination:(Some destination)
          ~site:(Mir_places.locate_site state origin)
      with
      | Some _ -> Definitions.raise_bug "a lending intrinsic that lends no part"
      | None -> ())
  | Capability_method { capability; name } ->
      let slot, signature = Targets.lookup_capability_method state.context capability name in
      let arguments =
        Mir_calls.evaluate_arguments state
          { signature with receiver = None }
          Types.no_substitution call.arguments
      in
      if Path.equal capability Definitions.panic_path then
        match (arguments, Lowering.find_panic_trace state) with
        | [ (_, _, message) ], Some trace ->
            ignore
              (Intrinsics.lower state.context.env state.builder state.context.types (Runtime Crash)
                 ~type_arguments:[] [ Intrinsics.Place message ] ~destination:None
                 ~site:(Mir_places.locate_site state origin)
                 ~trace:(Some trace))
        | [ _ ], None when state.frame.code.assumes_condition ->
            Lowering.emit_unreachable_block state
        | [ _ ], None -> Definitions.raise_bug "Panic.crash where Panic has no evidence"
        | _ -> Definitions.raise_bug "Panic.crash takes one message"
      else begin
        let c_signature, result = Targets.make_entry_signature state.context signature in
        let target =
          Lowered.Evidence_call
            {
              evidence = Targets.lookup_evidence state capability;
              capability;
              slot;
              signature = c_signature;
            }
        in
        Emit_c.Ir_builder.emit state.builder
          (Call
             {
               target;
               arguments =
                 List.filter_map
                   (fun (mode, ty, place) -> Targets.pass state mode ty place)
                   arguments;
               result = Convention.make_destination result destination;
             });
        if not c_signature.returns then Lowering.emit_unreachable_block state
      end
  | Indirect function_value ->
      let function_type =
        match Mir_places.compute_operand_type state function_value with
        | Function function_type -> function_type
        | callee_ty -> Definitions.raise_bug "a call of %s" (Ground.to_string callee_ty)
      in
      let value = Mir_places.lower_operand_place state function_value in
      Targets.lower_indirect_call state ~function_type ~value
        ~site:(Some (Mir_places.locate_site state origin))
        (List.map
           (fun argument ->
             let _, _, place = Mir_calls.lower_argument_place state argument in
             place)
           call.arguments)
        destination

and check_invariant state ~value ~clause ~destination =
  let _, value_ty, value_place = Mir_calls.lower_argument_place state value in
  let index =
    match clause with
    | { value = Immediate { value = Integer index; _ }; _ } -> Z.to_int index
    | _ -> Definitions.raise_bug "holds_invariant with a clause that is not a literal"
  in
  let path =
    match value_ty with
    | Named { path; _ } -> path
    | ty ->
        Definitions.raise_bug "holds_invariant of %s, which has no invariant" (Ground.to_string ty)
  in
  let ({ source; form = clauses } : Mir.type_clauses Mir.sourced) =
    match Mir.read_type_clauses state.context.lookups.mir path with
    | Some clauses -> clauses
    | None -> Definitions.raise_bug "%s has no clauses" (Path.show path)
  in
  let invariant =
    match List.nth_opt clauses.invariants index with
    | Some { clause; is_executable = true; _ } -> Mir.expand_formula clause
    | Some { is_executable = false; _ } | None ->
        Definitions.raise_bug "%s has no clause %d that runs" (Path.show path) index
  in
  Targets.run_in_type_definition state ~source value_ty (fun () ->
      lower_mir_into ~arguments:[ value_place ] state invariant destination)

and lend ?(forwards = 0) state part (call : Mir.call) ~origin =
  match
    (call.callee.target, if forwards < 8 then Mir_lends.find_forwarded_call state call else None)
  with
  | Intrinsic { operation; type_arguments }, _ ->
      Hashtbl.replace (Mir_places.require_mir_frame state).placed_parts part ();
      Lowering.run_in_statement state (fun () ->
          match
            Mir_calls.lower_intrinsic state operation ~type_arguments call.arguments
              ~destination:None
              ?reported:(Mir_places.find_reported_site state)
              ~site:(Mir_places.locate_site state origin)
          with
          | Some place -> Mir_places.bind_local state part place
          | None -> Definitions.raise_bug "a lent place from an intrinsic that does not lend")
  | _, Some { setup; lent } -> (
      List.iter
        (fun (local, type_, (computing : Mir.call)) ->
          let destination = Lowering.allocate_local state (Value (Lowering.ground state type_)) in
          Hashtbl.replace (Mir_places.require_mir_frame state).places local destination;
          lower_call_into state computing destination ~origin)
        setup;
      match lent with
      | Call inner -> lend ~forwards:(forwards + 1) state part inner ~origin
      | Place place ->
          Hashtbl.replace (Mir_places.require_mir_frame state).placed_parts part ();
          Lowering.run_in_statement state (fun () ->
              Mir_places.bind_local state part (Mir_places.lower_place state place)))
  | callee, None ->
      let frame = Mir_places.require_mir_frame state in
      let list_lent_operands part_ty : Lowered.operand list =
        (if Lowering.is_zero_size state part_ty then []
         else
           [
             (match frame.lending with
             | Some { slot = Some slot; part = own; _ }
               when Mir_lends.is_forwarded_whole frame part && own = part_ty ->
                 Lowered.Copy slot
             | Some _ when List.mem part frame.ended_after_lend -> Constant Null
             | _ ->
                 Address { place = Lowering.allocate_local state (Value part_ty); writable = true });
           ])
        @ [
            Mir_lends.obtain_lend_record state part;
            Mir_lends.obtain_lend_arena state;
            Option.value
              (Mir_places.find_reported_site state)
              ~default:(Constant (Site (Mir_places.locate_site state origin)));
          ]
      in
      let compute_lent_place (output : Types.result) substitution emit_call =
        let mode, part_ty =
          match output with
          | Lends (mode, ty) -> (mode, Monomorphic.ground state.context.monomorphic substitution ty)
          | Returns _ -> Definitions.raise_bug "a lending call of a method that does not lend"
        in
        if Lowering.is_zero_size state part_ty then begin
          emit_call ~lending:(list_lent_operands part_ty) (Mir_places.make_discard_place state);
          Lowering.allocate_local state (Value part_ty)
        end
        else begin
          let pointer =
            Lowering.allocate_local state
              (Pointer { target = Value part_ty; writable = mode = Mut })
          in
          emit_call ~lending:(list_lent_operands part_ty) pointer;
          Lowered.project pointer Deref
        end
      in
      let place =
        match callee with
        | Function _ | Trait_method _ ->
            let path, instantiation = Mir_calls.resolve_item state call.callee in
            let signature, substitution =
              Mir_calls.read_callee_signature state path instantiation
            in
            let arguments =
              Mir_calls.evaluate_arguments state signature substitution call.arguments
            in
            compute_lent_place signature.output substitution (fun ~lending destination ->
                Targets.lower_item_call state
                  (Lowered.Item.make_code path instantiation)
                  ~signature ~substitution ~arguments ~lending ~destination
                  ~site:(Some (Mir_places.locate_site state origin))
                  ())
        | Capability_method { capability; name } ->
            Targets.raise_lending_capability_method capability name
        | Indirect _ ->
            Definitions.raise_bug "a lending call of a function value, whose type cannot lend"
        | Intrinsic _ -> Definitions.raise_bug "a lending call of an intrinsic that lends no part"
      in
      Mir_places.bind_local state part place

and lend_part state ~(mode : Language.Mode.t) (part : Mir.yielded) =
  let frame = Mir_places.require_mir_frame state in
  let lending =
    match frame.lending with
    | Some lending -> lending
    | None -> Definitions.raise_bug "a part lent outside a lending method"
  in
  let owns = Moves.owns frame.moves in
  let outlives =
    Mir_lends.outlives_call ~owns
      ~is_view:(fun ty ->
        (Interface.Impls.is_view state.context.lookups.interface
           ~list_bounds:Interface.Impls.list_no_bounds)
          (Types.substitute state.frame.code.substitution ty))
      frame.body
  in
  let find_lent_in_place (written : Mir.place) : Lowered.place option =
    let lowered = Mir_places.lower_place state written in
    if outlives written && Lowering.is_reached_through_pointer state lowered then Some lowered
    else None
  in
  let rec write (yielded : Mir.yielded) (destination : Lowered.place) : lent_value =
    match yielded with
    | Part operand -> (
        let ty = Mir_places.compute_operand_type state operand in
        let owned = make_owned state ty in
        match operand with
        | Borrow { place = { root = Local local; projections = [] } as written; _ } when owns local
          ->
            Lowering.take state (Mir_places.lower_place state written) ty ~destination;
            owned
        | Borrow { place = written; _ } ->
            Emit_c.Ir_builder.emit state.builder
              (Assign (destination, Use (Copy (Mir_places.lower_place state written))));
            Holds_lent_places
              (match (find_lent_in_place written, mode) with
              | Some source, Mut -> [ ([], Deferred_write_back { source; ty }) ]
              | Some _, (Read | Own) -> []
              | None, Mut when outlives written ->
                  Definitions.raise_bug "a place lent `mut` that is not reached through a pointer"
              | None, _ ->
                  if not (outlives written || Lowering.is_trivial state ty) then
                    Definitions.raise_bug "a lent part of %s that the method owns"
                      (Ground.to_string ty);
                  [])
        | Use _ | Take _ | Immediate _ ->
            Mir_places.write_operand state operand destination;
            owned)
    | Built { variant; fields; type_; _ } ->
        let ty = Lowering.ground state type_ in
        let field_types = List.assoc variant (Mir_places.list_variants state ty) in
        let built =
          List.map
            (fun (name, (field : Mir.yielded option)) ->
              let field_ty = List.assoc name field_types in
              let value = Lowering.allocate_local state (Value field_ty) in
              let field_value =
                match field with
                | Some field -> write field value
                | None ->
                    let default, default_ty =
                      lower_field_default_place state ty ~variant ~field:name
                    in
                    Lowering.take state default default_ty ~destination:value;
                    make_owned state default_ty
              in
              ( (name, if Lowering.is_trivial state field_ty then Lowered.Copy value else Move value),
                field_value ))
            fields
        in
        Emit_c.Ir_builder.emit state.builder
          (Assign (destination, Build { ty; variant; fields = List.map fst built }));
        let is_indirect =
          match variant with
          | Some variant -> Memory_layout.is_indirect state.context.env ty variant
          | None -> false
        in
        let field_values = List.map snd built in
        let needs_no_drop =
          mode = Read && (not is_indirect)
          && List.for_all (fun value -> list_deferred value = []) field_values
        in
        if List.for_all (function Owned _ -> true | Holds_lent_places _ -> false) field_values
        then if needs_no_drop then Owned { dropped_as = None } else make_owned state ty
        else
          Holds_lent_places
            ((match variant with
               | Some variant when is_indirect -> [ ([], Deferred_free variant) ]
               | _ -> [])
            @ List.concat_map
                (fun ((name, _), field_value) ->
                  List.map
                    (fun (inside, deferred) ->
                      (Mir_places.make_field_projection variant name :: inside, deferred))
                    (list_deferred field_value))
                built)
  in
  let defer_call intrinsic arguments =
    Emit_c.Ir_builder.emit state.builder
      (Call
         {
           target = Intrinsic intrinsic;
           arguments = lending.record :: lending.arena :: arguments;
           result = Discarded;
         })
  in
  let take_address place : Lowered.operand = Address { place; writable = true } in
  let defer (slot : Lowered.place) (inside, deferred) =
    let target = List.fold_left Lowered.project slot inside in
    match deferred with
    | Deferred_drop ty ->
        defer_call Lend_defer_drop
          [ Constant (Symbol_address (Untyped_drop ty)); take_address target ]
    | Deferred_write_back { source; ty } ->
        defer_call Lend_defer_write_back
          [ take_address source; take_address target; Constant (Size_of ty) ]
    | Deferred_free variant ->
        Emit_c.Ir_builder.emit state.builder
          (Defer_free_block
             { lend = lending.record; arena = lending.arena; place = target; variant })
  in
  Mir_lends.transfer_lends state lending;
  match lending.slot with
  | None -> ()
  | Some slot_pointer -> (
      let pointer : Lowered.operand =
        match part with
        | Part (Borrow { place = written; _ }) when find_lent_in_place written <> None ->
            Address { place = Option.get (find_lent_in_place written); writable = mode = Mut }
        | _ ->
            Emit_c.Ir_builder.emit_when state.builder
              (Test (Equal, Copy slot_pointer, Constant Null))
              (fun () ->
                Emit_c.Ir_builder.emit state.builder
                  (Call
                     {
                       target = Intrinsic Lend_allocate;
                       arguments =
                         [
                           lending.record;
                           lending.arena;
                           Constant (Size_of lending.part);
                           Constant (Alignment_of lending.part);
                         ];
                       result = Returned slot_pointer;
                     }));
            let slot = Lowered.project slot_pointer Deref in
            List.iter (defer slot) (list_deferred (write part slot));
            Address { place = slot; writable = mode = Mut }
      in
      match Lowering.find_result_place state with
      | Some result -> Emit_c.Ir_builder.emit state.builder (Assign (result, Use pointer))
      | None -> Definitions.raise_bug "a lending method with no result")

and lower_terminator state (region : Mir_drops.region) (ending : Mir.Graph.terminator) ~origin =
  match ending with
  | Goto target -> Mir_drops.goto state region target
  | Branch { condition; yes; no; _ } ->
      let condition =
        Lowering.run_in_statement state (fun () -> Mir_places.lower_operand state condition)
      in
      let yes = Mir_drops.resolve_jump state region yes
      and no = Mir_drops.resolve_jump state region no in
      Emit_c.Ir_builder.branch state.builder (Holds condition) ~yes ~no;
      Emit_c.Ir_builder.start state.builder (Emit_c.Ir_builder.allocate_block state.builder)
  | Unreachable | Written_unreachable -> Lowering.emit_unreachable_block state
  | Todo ->
      let message = "todo reached" in
      Emit_c.Ir_builder.finish state.builder
        (Fail
           {
             failure = Todo;
             message = Constant (Bytes message);
             length = Lowered.make_uint64_constant (String.length message);
             site = Mir_places.locate_site state origin;
             reported = None;
             trace = None;
           });
      Emit_c.Ir_builder.start state.builder (Emit_c.Ir_builder.allocate_block state.builder)
  | Return returned ->
      (let frame = Mir_places.require_mir_frame state in
       frame.move_state_at_return <- Some (Moves.copy frame.move_state));
      (match (Mir_places.find_result_slot state, returned) with
      | Some _, Some (Use { place = { root = Local local; projections = [] }; _ })
        when List.mem local (Mir_places.require_mir_frame state).returned ->
          ()
      | Some slot, Some returned ->
          Lowering.run_in_statement state (fun () -> Mir_places.write_operand state returned slot)
      | _ -> ());
      Mir_drops.return_from_frame state
  | Iteration_end _ -> Mir_drops.continue_loop state
  | Cancel { task; task_end; winner; number; returned } ->
      Option.iter
        (fun target ->
          let rec locate_branch_region (around : Mir_drops.region) =
            match (around.ending, task, around.enclosing) with
            | Some (ending, _), Branch { fork; _ }, _ when ending = fork -> around
            | _, _, Some enclosing -> locate_branch_region enclosing
            | _, _, None -> Definitions.raise_bug "an early exit from a branch outside its block"
          in
          let branch = locate_branch_region region in
          ignore (Mir_drops.resolve_jump ~entry:branch.start state branch target))
        task_end;
      let value =
        Option.map
          (fun (returned, slot) ->
            let ty = Lowering.ground state (Mir_places.lookup_local_info state slot).type_ in
            let value =
              Lowered.make_local_place (Emit_c.Ir_builder.allocate_local state.builder (Value ty))
            in
            Mir_places.write_operand state returned value;
            (value, ty, slot))
          returned
      in
      Mir_tasks.cancel state ~task ~winner ~number ~value
  | Resume { winner; exits; next } ->
      let cases =
        List.mapi
          (fun index (exit : Mir.Graph.early_exit) ->
            (Z.of_int (index + 1), Mir_drops.resolve_jump state region exit.resume))
          exits
      in
      Emit_c.Ir_builder.finish state.builder
        (Switch
           {
             value = Copy (Mir_places.lookup_local_place state winner);
             cases;
             default = Mir_drops.resolve_jump state region next;
           });
      Emit_c.Ir_builder.start state.builder (Emit_c.Ir_builder.allocate_block state.builder)
  | Yield { mode; part; resume } ->
      Lowering.run_in_statement state (fun () -> lend_part state ~mode part);
      Mir_drops.goto state region resume
  | For { iteration; part; body; after; loop; _ } ->
      Mir_drops.claim state region after;
      lower_for_loop state region ~iteration ~part ~body ~loop;
      Mir_drops.goto state region after
  | Fork { fork; concurrent = true; branches; join } ->
      lower_concurrent_block state region ~fork ~branches ~join
  | Fork { fork; concurrent = false; branches; join } -> (
      match branches with
      | [] -> Lowering.emit_unreachable_block state
      | first :: _ when not (Lowering.may_fork state) -> Mir_drops.goto state region first.entry
      | _ -> (
          let forked =
            List.map
              (fun (branch : Mir.Graph.branch) ->
                Lowering.outline state ~parts:[] (fun () ->
                    let end_block = Emit_c.Ir_builder.allocate_block state.builder in
                    run_region state
                      (Mir_drops.make_region state ~enclosing:region ~ending:(fork, end_block))
                      ~entry:(branch.entry, 0);
                    Emit_c.Ir_builder.finish state.builder (Goto end_block);
                    Emit_c.Ir_builder.start state.builder end_block;
                    Emit_c.Ir_builder.finish state.builder (Return None)))
              branches
          in
          Emit_c.Ir_builder.emit state.builder (Fork { branches = forked });
          match join with
          | Some join -> Mir_drops.goto state region join
          | None -> Lowering.emit_unreachable_block state))
  | Join { fork; next } -> (
      match region.ending with
      | Some (ending, end_block) when ending = fork ->
          Emit_c.Ir_builder.finish state.builder (Goto end_block);
          Emit_c.Ir_builder.start state.builder (Emit_c.Ir_builder.allocate_block state.builder)
      | _ -> Mir_drops.goto state region next)

and lower_loop_body (state : Lowering.state) (region : Mir_drops.region) ~part ~body
    (value : Lowered.place) =
  let caller = state.frame in
  state.frame <- region.region_frame;
  Mir_places.bind_local state part value;
  let inner = Mir_drops.make_region ~enclosing:region state in
  state.frame <- caller;
  run_region state inner ~entry:(body, 0)

and lower_for_loop state (region : Mir_drops.region) ~(iteration : Mir.iteration) ~part ~body
    ~(loop : Mir.loop) =
  let origin = loop.origin in
  let task : Mir.task = Iteration { loop = loop.node } in
  let each = lower_loop_body state region ~part ~body in
  match loop.schedule with
  | Concurrent ->
      Mir_tasks.with_group state (fun group ->
          let spawning =
            {
              Lowering.task;
              group;
              item =
                Emit_c.Ir_builder.allocate_local state.builder (Value (Ground.make_builtin UInt64));
              element = Lowering.ground state (Mir_places.lookup_local_info state part).type_;
            }
          in
          Mir_loops.lower_for_each state ~schedule:(Spawned spawning) ~iteration ~each ~origin)
  | Parallel -> Mir_loops.lower_for_each state ~schedule:Chunked ~iteration ~each ~origin
  | Language.Loop_mode.Sequential ->
      Mir_loops.lower_for_each state ~schedule:Sequential ~iteration ~each ~origin

let lower_code (state : Lowering.state) path ~parameters ?lending () =
  let code_mir = Loop_parts.end_parts (Mir_places.read_mir_graph state.context path) in
  let frame =
    Mir_places.make_body_frame state
      ~owner:(Lowering.lookup_innermost_scope state)
      ?lending ~lambdas:code_mir.lambdas code_mir.body
  in
  state.frame <- { state.frame with mir = Some frame };
  Option.iter (fun (lending : Lowering.lending) -> state.lend_arena <- Some lending.arena) lending;
  List.iter2 (Mir_places.bind_local state) code_mir.body.parameters parameters;
  Mir_lends.make_owned_locals state;
  lower_body state frame
