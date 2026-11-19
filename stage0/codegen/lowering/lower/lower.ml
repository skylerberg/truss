type unsupported = Lowering.unsupported = { construct : string; at : Lowered.site option }

exception Unsupported = Lowering.Unsupported

type context = Definitions.context

let env (context : context) = context.env
let drop_and_copy (context : context) = context.drop_and_copy
let make_monomorphic_context = Definitions.make_monomorphic_context
let make_context = Definitions.make_context

type constant = Constants.constant = Folded of Lowered.data | Run of Ground.ty

let lower_constant = Constants.compile_constant
let lower_evaluator = Constants.build_evaluator
let lower_generated = Generated.lower
let lower_table = Generated.lower_table

let bind_parameters state (body : Mir.Graph.body) ~(defaults : (int * Mir.Graph.t) list) =
  let filled = ref 0 in
  List.mapi
    (fun position local ->
      let mode, name, type_ = Mir_places.extract_parameter body local in
      let ty = Lowering.ground state type_ in
      let bit =
        Option.map
          (fun _ ->
            incr filled;
            !filled - 1)
          (List.assoc_opt position defaults)
      in
      let arrives, place =
        Lowering.allocate_parameter state ~in_scope:false ?name
          ~owned:(mode = Own && bit = None)
          mode ty
      in
      (arrives, bit, place))
    body.parameters

let begin_body (state : Lowering.state) ~(body : Mir.Graph.body) ~defaults =
  let code = state.frame.code in
  let bound = bind_parameters state body ~defaults in
  let places = List.map (fun (_, _, place) -> place) bound in
  let mask =
    if code.has_defaults then
      Some (Emit_c.Ir_builder.allocate_local state.builder (Raw (Integer UInt64)))
    else None
  in
  let evidence =
    Lowering.list_evidence_parameters state
      (Definitions.list_evidence state.context code.substitution code.uses)
  in
  Emit_c.Ir_builder.start state.builder (Emit_c.Ir_builder.allocate_block state.builder);
  let places =
    match mask with
    | Some mask ->
        Mir_form.fill_defaults state (Lowered.make_local_place mask) body ~defaults places
    | None -> places
  in
  (List.filter_map (fun (arrives, _, _) -> arrives) bound @ Option.to_list mask @ evidence, places)

let make_code_state context ~item path =
  let code = Definitions.make_code context path Ground.no_instantiation in
  (Lowering.enter_item context ~item code, code)

let lower_template_check context ~from_template ~literals ~clauses : Emit_c.fragment =
  let item = Lowered.Item.Template_check { from_template; literals; clauses } in
  let state, _ = make_code_state context ~item from_template in
  let template_type =
    match
      Definitions.list_interface_parameters (Definitions.read_signature context from_template)
    with
    | [ (_, template_type) ] -> template_type
    | _ -> Definitions.raise_bug "%s does not take one template" (Path.show from_template)
  in
  Emit_c.Ir_builder.start state.builder (Emit_c.Ir_builder.allocate_block state.builder);
  Lowering.run_in_scope state (fun () ->
      let template =
        Targets.lower_template_value state
          (Lowering.ground state template_type)
          literals
          ~site:{ definition = state.frame.code.definition; offset = 0 }
          ~parts:[]
      in
      let output = Targets.begin_output state in
      List.iter
        (fun clause ->
          let holds = Lowering.allocate_temporary state context.bool in
          Mir_form.lower_mir_into ~arguments:[ template ] state clause holds;
          Encoding.encode_call context.env state.builder
            ~output:(Address { place = output; writable = true })
            context.bool holds)
        (Definitions.list_template_clauses context from_template clauses);
      Constants.write_output state output);
  Lowering.finish_item state ~rest:[] ()

let lower_call_evaluation context ~function_ ~arguments : Emit_c.fragment =
  let item = Lowered.Item.Call_evaluation { function_; arguments } in
  let state, _ = make_code_state context ~item function_ in
  Emit_c.Ir_builder.start state.builder (Emit_c.Ir_builder.allocate_block state.builder);
  let signature = Definitions.read_signature context function_ in
  Lowering.run_in_scope state (fun () ->
      let passed =
        List.map2
          (fun (mode, ty) value ->
            let ty = Lowering.ground state ty in
            let place = Lowering.allocate_temporary state ty in
            let constant =
              match Lowering.classify_scalar state ty with
              | Integer integer -> Lowering.make_int_constant integer value
              | Bool -> Lowered.Constant (Bool (not (Z.equal value Z.zero)))
              | _ ->
                  Definitions.raise_bug "an evaluated call's argument of type %s"
                    (Ground.to_string ty)
            in
            Emit_c.Ir_builder.emit state.builder (Assign (place, Use constant));
            (mode, ty, place))
          (Definitions.list_interface_parameters signature)
          arguments
      in
      let result_ty =
        match signature.output with
        | Returns ty -> Lowering.ground state ty
        | _ -> Definitions.raise_bug "an evaluated call that does not return"
      in
      let result = Lowering.allocate_temporary state result_ty in
      Targets.lower_item_call state
        (Code { path = function_; instantiation = Ground.no_instantiation })
        ~signature ~substitution:Types.no_substitution ~arguments:passed ~destination:result
        ~site:None ();
      let output = Targets.begin_output state in
      Encoding.encode_call context.env state.builder
        ~output:(Address { place = output; writable = true })
        result_ty result;
      Constants.write_output state output);
  Lowering.finish_item state ~rest:[] ()

let lower_source_code context ~path ~instantiation : Emit_c.fragment =
  let item = Lowered.Item.Code { path; instantiation } in
  let code = Definitions.make_code context path instantiation in
  let body = (Mir_places.read_mir_graph context path).body in
  let state = Lowering.enter_item context ~item code in
  let convention, returns = Definitions.classify_result context code.substitution code.result in
  Lowering.set_result_slot state convention;
  let parameter_locals, places =
    begin_body state ~body ~defaults:(Mir_places.read_parameter_defaults context path).form
  in
  let lending_locals =
    List.map
      (fun ty -> Emit_c.Ir_builder.allocate_local state.builder ty)
      (Definitions.list_lending_parameters context code.substitution code.result)
  in
  let lending : Lowering.lending option =
    match (code.result, List.rev lending_locals) with
    | Lends (_, ty), site :: record :: slot ->
        Some
          {
            slot = (match slot with [ slot ] -> Some (Lowered.make_local_place slot) | _ -> None);
            part = Lowering.ground state ty;
            record = Copy (Lowered.make_local_place record);
            site = Copy (Lowered.make_local_place site);
          }
    | _ -> None
  in
  Mir_form.lower_code state path ~parameters:places ?lending ();
  Lowering.finish_item state ~returns ~rest:(parameter_locals @ lending_locals) ()
