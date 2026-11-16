open Emit_c.Builder
open Definitions
open Lowering
open Targets

type unsupported = Lowering.unsupported = { construct : string; at : Lowered.site option }

exception Unsupported = Lowering.Unsupported

type context = Definitions.context

let env (context : context) = context.env
let drop_and_copy (context : context) = context.drop_and_copy
let monomorphic = Definitions.monomorphic
let context = Definitions.context
let list_folded_constants = Constants.list_folded_constants
let test_key = Definitions.test_key

type constant = Constants.constant = Folded of Lowered.data | Run of Ground.ty

let lower_constant = Constants.constant
let lower_evaluator = Constants.evaluator
let lower_generated = Generated.lower
let lower_table = Generated.lower_table

let bind_parameters st (body : Mir.Graph.body) ~(defaults : (int * Mir.Graph.t) list) =
  let filled = ref 0 in
  List.mapi
    (fun position local ->
      let mode, _, type_ = Mir_form.parameter_of body local in
      let ty = ground st type_ in
      let bit =
        Option.map
          (fun _ ->
            incr filled;
            !filled - 1)
          (List.assoc_opt position defaults)
      in
      let arrives, place =
        Lowering.parameter st ~in_scope:false
          ~owned:(mode = Own && bit = None)
          (Monomorphic.mode mode) ty
      in
      (arrives, bit, place))
    body.parameters

let begin_body st ~(body : Mir.Graph.body) ~defaults =
  let code = st.frame.code in
  let bound = bind_parameters st body ~defaults in
  let places = List.map (fun (_, _, place) -> place) bound in
  let mask =
    if code.has_defaults then Some (local st.builder ~name:"passed" (Raw (Integer UInt64)))
    else None
  in
  let evidence = evidence_parameters st (evidence_for st.context code.substitution code.uses) in
  start st.builder (block st.builder);
  st.evidence <-
    st.evidence
    @ Generated.real_implementations st ~user:(Path.show code.definition_key.path) code.real;
  let places =
    match mask with
    | Some mask -> Mir_form.fill_defaults st (at mask) body ~defaults places
    | None -> places
  in
  (List.filter_map (fun (arrives, _, _) -> arrives) bound @ Option.to_list mask @ evidence, places)

let code_state context ~key path =
  let code = code_of context path [] in
  (enter context ~builder:(create context.env ~key) (frame_of code), code)

let lower_template_check context ~from_template ~literals ~clauses : Emit_c.Builder.instance =
  let key = Instance.Template_check { from_template; literals; clauses } in
  let st, _ = code_state context ~key from_template in
  let template_type =
    match interface_parameters (signature_of context from_template) with
    | [ (_, template_type) ] -> template_type
    | _ -> bug "%s does not take one template" (Path.show from_template)
  in
  start st.builder (block st.builder);
  in_scope st (fun () ->
      let template =
        template_value st (ground st template_type) literals
          ~site:{ definition = st.frame.code.definition_key.path; offset = 0 }
          ~parts:[]
      in
      let output = begin_output st in
      List.iter
        (fun clause ->
          let holds = temporary st context.bool in
          Mir_form.mir_into ~arguments:[ template ] st clause holds;
          Encoding.encode_call context.env st.builder
            ~output:(Address { place = output; writable = true })
            context.bool holds)
        (template_clauses context from_template clauses);
      Constants.write_output st output);
  finish_instance st ~rest:[] ()

let lower_call_evaluation context ~function_ ~arguments : Emit_c.Builder.instance =
  let key = Instance.Call_evaluation { function_; arguments } in
  let st, _ = code_state context ~key function_ in
  start st.builder (block st.builder);
  let signature = signature_of context function_ in
  in_scope st (fun () ->
      let passed =
        List.map2
          (fun (mode, ty) value ->
            let ty = ground st ty in
            let place = temporary st ty in
            let constant =
              match scalar_of st ty with
              | Integer integer -> constant_int integer value
              | Bool -> Lowered.Constant (Bool (not (Z.equal value Z.zero)))
              | _ -> bug "an evaluated call's argument of type %s" (Ground.to_string ty)
            in
            emit st.builder (Assign (place, Use constant));
            (mode, ty, place))
          (interface_parameters signature) arguments
      in
      let result_ty =
        match signature.output with
        | Returns ty -> ground st ty
        | _ -> bug "an evaluated call that does not return"
      in
      let result = temporary st result_ty in
      call_instance st
        (Code { path = function_; type_arguments = [] })
        ~signature ~substitution:[] ~arguments:passed ~destination:result ();
      let output = begin_output st in
      Encoding.encode_call context.env st.builder
        ~output:(Address { place = output; writable = true })
        result_ty result;
      Constants.write_output st output);
  finish_instance st ~rest:[] ()

let lower_source_code context ~path ~type_arguments : Emit_c.Builder.instance =
  let key = Instance.Code { path; type_arguments } in
  let code = code_of context path type_arguments in
  let body = (Mir_form.mir_of context path).body in
  let st = enter context ~builder:(create context.env ~key) (frame_of code) in
  let convention, returns = result_of context code.substitution code.result in
  result_slot st convention;
  let parameter_locals, places =
    begin_body st ~body ~defaults:(Mir_form.parameter_defaults context path)
  in
  let lending_locals =
    List.map
      (fun ty -> local st.builder ~name:"lend" ty)
      (lending_parameters context code.substitution code.result)
  in
  let lending : Lowering.lending option =
    match (code.result, List.rev lending_locals) with
    | Lends (_, ty), site :: record :: slot ->
        Some
          {
            slot = (match slot with [ slot ] -> Some (at slot) | _ -> None);
            part = ground st ty;
            record = Copy (at record);
            site = Copy (at site);
          }
    | _ -> None
  in
  Mir_form.lower_code st path ~parameters:places ?lending ();
  finish_instance st ~returns ~rest:(parameter_locals @ lending_locals) ()
