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

let bind_parameters st (body : Mir.Graph.body) ~(defaults : (int * Mir.Graph.t) list) =
  let filled = ref 0 in
  List.mapi
    (fun position local ->
      let mode, name, type_ = Mir_form.extract_parameter body local in
      let ty = Lowering.ground st type_ in
      let bit =
        Option.map
          (fun _ ->
            incr filled;
            !filled - 1)
          (List.assoc_opt position defaults)
      in
      let arrives, place =
        Lowering.allocate_parameter st ~in_scope:false ?name
          ~owned:(mode = Own && bit = None)
          (Monomorphic.ground_mode mode) ty
      in
      (arrives, bit, place))
    body.parameters

let begin_body (st : Lowering.state) ~(body : Mir.Graph.body) ~defaults =
  let code = st.frame.code in
  let bound = bind_parameters st body ~defaults in
  let places = List.map (fun (_, _, place) -> place) bound in
  let mask =
    if code.has_defaults then Some (Emit_c.Builder.allocate_local st.builder (Raw (Integer UInt64)))
    else None
  in
  let evidence =
    Lowering.list_evidence_parameters st
      (Definitions.list_evidence st.context code.substitution code.uses)
  in
  Emit_c.Builder.start st.builder (Emit_c.Builder.allocate_block st.builder);
  st.evidence <-
    st.evidence @ Generated.list_real_implementations st ~user:(Path.show code.definition) code.real;
  let places =
    match mask with
    | Some mask -> Mir_form.fill_defaults st (Lowered.make_local_place mask) body ~defaults places
    | None -> places
  in
  (List.filter_map (fun (arrives, _, _) -> arrives) bound @ Option.to_list mask @ evidence, places)

let make_code_state context ~key path =
  let code = Definitions.make_code context path [] in
  ( Lowering.enter context
      ~builder:(Emit_c.Builder.create context.env ~key)
      (Lowering.make_frame code),
    code )

let find_constant_literal (context : Definitions.context) ~definition ~origin =
  let list_sourced = function
    | Some ({ source; form } : Mir.Graph.t Mir.sourced) -> [ (source, form) ]
    | None -> []
  in
  let graphs =
    list_sourced (Mir.read_graph context.lookups.mir definition)
    @ list_sourced (Mir.read_initializer_graph context.lookups.mir definition)
    @
    match Mir.read_default_graphs context.lookups.mir definition with
    | Some { source; form = Parameter_defaults defaults } ->
        List.map (fun (_, graph) -> (source, graph)) defaults
    | Some { source; form = Field_defaults defaults } ->
        List.map (fun (default : Mir.Graph.t Mir.field_default) -> (source, default.value)) defaults
    | None -> []
  in
  let find_in (body : Mir.Graph.body) =
    Array.find_map
      (fun (block : Mir.Graph.basic_block) ->
        List.find_map
          (fun (statement : Mir.Graph.statement) ->
            match statement.kind with
            | Checked_literal { subject = Constant_argument argument; call; _ }
              when statement.origin = origin ->
                Some (call, argument)
            | _ -> None)
          block.statements)
      body.blocks
  in
  match
    List.find_map
      (fun (source, (graph : Mir.Graph.t)) ->
        Option.map
          (fun (call, argument) -> (source, call, argument))
          (List.find_map find_in (graph.body :: Array.to_list graph.lambdas)))
      graphs
  with
  | Some literal -> literal
  | None ->
      Definitions.raise_bug "%s has no constant literal at node %d" (Path.show definition) origin

let lower_literal_check context (check : Instance.literal_check) : Emit_c.Builder.instance =
  let key = Instance.Literal_check check in
  let subject_type =
    match
      Definitions.list_interface_parameters (Definitions.read_signature context check.method_)
    with
    | [ (_, subject_type) ] -> subject_type
    | _ -> Definitions.raise_bug "%s does not take one value" (Path.show check.method_)
  in
  let run_clauses (st : Lowering.state) subject =
    let output = Targets.begin_output st in
    List.iter
      (fun clause ->
        let holds = Lowering.allocate_temporary st context.bool in
        Mir_form.lower_mir_into ~arguments:[ subject ] st clause holds;
        Encoding.encode_call context.env st.builder
          ~output:(Address { place = output; writable = true })
          context.bool holds)
      (Definitions.list_runnable_requires context check.method_ check.clauses);
    Constants.write_output st output
  in
  match check.subject with
  | Template_text literals ->
      let st, _ = make_code_state context ~key check.method_ in
      Emit_c.Builder.start st.builder (Emit_c.Builder.allocate_block st.builder);
      Lowering.run_in_scope st (fun () ->
          run_clauses st
            (Targets.lower_template_value st (Lowering.ground st subject_type) literals
               ~site:{ definition = st.frame.code.definition; offset = 0 }
               ~parts:[]));
      Lowering.finish_instance st ~rest:[] ()
  | Constant_argument { definition; origin } ->
      let source, call, argument = find_constant_literal context ~definition ~origin in
      let type_arguments =
        match call.callee with
        | Trait_method { trait; name; receiver; self_type; type_arguments; evidence } -> (
            match
              Targets.make_trait_method_key context [] ~trait ~name ~receiver ~self_type
                ~type_arguments ~evidence
            with
            | Code { type_arguments; _ } -> type_arguments
            | _ -> Definitions.raise_bug "%s is not code" (Path.show check.method_))
        | _ ->
            Definitions.raise_bug "the constant literal at node %d of %s calls no trait method"
              origin (Path.show definition)
      in
      let st =
        Lowering.enter context
          ~builder:(Emit_c.Builder.create context.env ~key)
          (Lowering.make_frame (Definitions.make_code context check.method_ type_arguments))
      in
      let literal_state =
        Lowering.enter context ~builder:st.builder
          (Lowering.make_frame
             {
               (Definitions.make_unwritten_code ~definition:source.path ~substitution:[]
                  ~result:(Returns Types.unit))
               with
               written = Some (Definitions.read_written context source);
             })
      in
      Emit_c.Builder.start st.builder (Emit_c.Builder.allocate_block st.builder);
      Lowering.run_in_scope st (fun () ->
          let elements = Lowering.allocate_temporary st (Lowering.ground st subject_type) in
          Mir_form.lower_mir_into literal_state (Mir.expand_formula argument) elements;
          run_clauses st elements);
      Lowering.finish_instance st ~rest:[] ()

let lower_call_evaluation context ~function_ ~arguments : Emit_c.Builder.instance =
  let key = Instance.Call_evaluation { function_; arguments } in
  let st, _ = make_code_state context ~key function_ in
  Emit_c.Builder.start st.builder (Emit_c.Builder.allocate_block st.builder);
  let signature = Definitions.read_signature context function_ in
  Lowering.run_in_scope st (fun () ->
      let passed =
        List.map2
          (fun (mode, ty) value ->
            let ty = Lowering.ground st ty in
            let place = Lowering.allocate_temporary st ty in
            let constant =
              match Lowering.classify_scalar st ty with
              | Integer integer -> Lowering.make_int_constant integer value
              | Bool -> Lowered.Constant (Bool (not (Z.equal value Z.zero)))
              | _ ->
                  Definitions.raise_bug "an evaluated call's argument of type %s"
                    (Ground.to_string ty)
            in
            Emit_c.Builder.emit st.builder (Assign (place, Use constant));
            (mode, ty, place))
          (Definitions.list_interface_parameters signature)
          arguments
      in
      let result_ty =
        match signature.output with
        | Returns ty -> Lowering.ground st ty
        | _ -> Definitions.raise_bug "an evaluated call that does not return"
      in
      let result = Lowering.allocate_temporary st result_ty in
      Targets.lower_instance_call st
        (Code { path = function_; type_arguments = [] })
        ~signature ~substitution:[] ~arguments:passed ~destination:result ();
      let output = Targets.begin_output st in
      Encoding.encode_call context.env st.builder
        ~output:(Address { place = output; writable = true })
        result_ty result;
      Constants.write_output st output);
  Lowering.finish_instance st ~rest:[] ()

let lower_source_code context ~path ~type_arguments : Emit_c.Builder.instance =
  let key = Instance.Code { path; type_arguments } in
  let code = Definitions.make_code context path type_arguments in
  let body = (Mir_form.read_mir_graph context path).body in
  let st =
    Lowering.enter context
      ~builder:(Emit_c.Builder.create context.env ~key)
      (Lowering.make_frame code)
  in
  let convention, returns = Definitions.classify_result context code.substitution code.result in
  Lowering.set_result_slot st convention;
  let parameter_locals, places =
    begin_body st ~body ~defaults:(Mir_form.read_parameter_defaults context path).form
  in
  let lending_locals =
    List.map
      (fun ty -> Emit_c.Builder.allocate_local st.builder ty)
      (Definitions.list_lending_parameters context code.substitution code.result)
  in
  let lending : Lowering.lending option =
    match (code.result, List.rev lending_locals) with
    | Lends (_, ty), site :: record :: slot ->
        Some
          {
            slot = (match slot with [ slot ] -> Some (Lowered.make_local_place slot) | _ -> None);
            part = Lowering.ground st ty;
            record = Copy (Lowered.make_local_place record);
            site = Copy (Lowered.make_local_place site);
          }
    | _ -> None
  in
  Mir_form.lower_code st path ~parameters:places ?lending ();
  Lowering.finish_instance st ~returns ~rest:(parameter_locals @ lending_locals) ()
