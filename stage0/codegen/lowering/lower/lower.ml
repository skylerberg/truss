type unsupported = Lowering.unsupported = {
  construct : Catalog.Codegen.construct;
  at : Lowered.site option;
}

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

let begin_body (state : Lowering.state) ~(body : Mir.Graph.body) =
  let code = state.frame.code in
  let bound =
    List.map
      (fun local ->
        let mode, name, type_ = Mir_places.extract_parameter body local in
        Lowering.allocate_parameter state ~in_scope:false ?name ~owned:(mode = Own) mode
          (Lowering.ground state type_))
      body.parameters
  in
  let evidence =
    Lowering.list_evidence_parameters state
      (Definitions.list_evidence state.context code.substitution code.uses)
  in
  Emit_c.Ir_builder.start state.builder (Emit_c.Ir_builder.allocate_block state.builder);
  (List.filter_map fst bound @ evidence, List.map snd bound)

let lower_source_code context ~path ~instantiation ~assumed : Emit_c.fragment =
  let item = Lowered.Item.Code { path; instantiation; assumed } in
  let code = Definitions.make_code context path instantiation in
  let code =
    {
      code with
      uses = Definitions.remove_assumed context code.substitution ~assumed code.uses;
      assumed;
    }
  in
  let body = (Mir_places.read_mir_graph context path).body in
  let state = Lowering.enter_item context ~item code in
  let convention, returns = Definitions.classify_result context code.substitution code.result in
  Lowering.set_result_slot state convention;
  let parameter_locals, places = begin_body state ~body in
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
