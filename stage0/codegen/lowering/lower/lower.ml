type unsupported = Lowering.unsupported = { construct : string; at : Lowered.site option }

exception Unsupported = Lowering.Unsupported

type context = Definitions.context

let env (context : context) = context.env
let drop_and_copy (context : context) = context.drop_and_copy
let make_monomorphic_context = Definitions.make_monomorphic_context
let make_context = Definitions.make_context

type evaluated = Constants.evaluated = Folded of Lowered.data | Run of Ground.ty

let lower_evaluated = Constants.compile
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

let lower_source_code context ~path ~instantiation ~assumes_condition : Emit_c.fragment =
  let item = Lowered.Item.Code { path; instantiation; assumes_condition } in
  let code = Definitions.make_code context path instantiation in
  let code =
    if assumes_condition then
      { code with uses = Definitions.remove_panic_condition code.uses; assumes_condition }
    else code
  in
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
