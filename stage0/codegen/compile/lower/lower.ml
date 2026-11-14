(* Lowering: the core form of one instance to its C. *)

open Emit_c.Builder
open Definitions
open Lowering
open Targets
open Generated

type unsupported = Lowering.unsupported = { construct : string; at : Lowered.site option }

exception Unsupported = Lowering.Unsupported

type context = Definitions.context

let env (context : context) = context.env
let glue (context : context) = context.glue
let monomorphic (context : context) = context.monomorphic
let constant_value (context : context) = context.constant
let context = Definitions.context
let test_key = Definitions.test_key

type constant = Constants.constant = Folded of Lowered.data | Run of Ground.ty

let constant = Constants.constant
let evaluator = Constants.evaluator
let table = Generated.table
let locked_table = Generated.locked_table
let any_table = Generated.any_table

let bind_parameters st (body : Mir.body) =
  let defaults = ref 0 in
  List.map
    (fun local ->
      let mode, _, type_ = Mir_form.parameter_of body local in
      let ty = ground st type_ in
      let bit =
        Option.map
          (fun _ ->
            incr defaults;
            !defaults - 1)
          (List.assoc_opt local body.defaults)
      in
      let arrives, place =
        Lowering.parameter st ~in_scope:false
          ~owned:(mode = Own && bit = None)
          (Monomorphic.mode mode) ty
      in
      (arrives, bit, place))
    body.parameters

let begin_body st ~(body : Mir.body) =
  let code = st.frame.code in
  let bound = bind_parameters st body in
  let places = List.map (fun (_, _, place) -> place) bound in
  let mask =
    if code.has_defaults then Some (local st.builder ~name:"passed" (Raw (Integer UInt64)))
    else None
  in
  let evidence = evidence_parameters st (evidence_for st.context code.substitution code.uses) in
  start st.builder (block st.builder);
  st.evidence <-
    st.evidence @ Generated.real_implementations st ~user:(Path.show code.anchor) code.real;
  let places =
    match mask with Some mask -> Mir_form.fill_defaults st (at mask) body places | None -> places
  in
  (List.filter_map (fun (arrives, _, _) -> arrives) bound @ Option.to_list mask @ evidence, places)

let code_state context ~key path =
  let code = code_of context path [] in
  (enter context ~builder:(create context.env ~key) (frame_of code ~inlined:[ path ]), code)

(* A tag's [from_template]: its one parameter and its [requires] clauses,
   from its core form. *)
let from_template_contract context from_template : Core.parameter * Core.condition list =
  match demand context Infer.core_of_path from_template with
  | Some ({ definition = Function { parameters = [ parameter ]; contract; _ }; _ }, _) ->
      (parameter, contract.requires)
  | _ -> bug "%s does not take one template" (Path.show from_template)

let template_checked context from_template =
  let _, requires = from_template_contract context from_template in
  List.concat
    (List.mapi
       (fun index (clause : Core.condition) -> if clause.executable then [ index ] else [])
       requires)

let template_check context (key : Instance.key) ~from_template ~texts : Emit_c.Builder.instance =
  let st, _ = code_state context ~key from_template in
  let parameter, requires = from_template_contract context from_template in
  start st.builder (block st.builder);
  in_scope st (fun () ->
      let template =
        template_value st (ground st parameter.type_) texts
          ~site:{ definition = st.frame.code.anchor; line = 1; column = 1 }
          ~parts:[]
      in
      let output = Constants.begin_output st in
      List.iter
        (fun (clause : Core.condition) ->
          if clause.executable then begin
            let holds = temporary st context.bool in
            Mir_form.expression_into ~arguments:[ (parameter, template) ] st clause.value holds;
            Glue.encode_call context.glue st.builder
              ~output:(Address { place = output; writable = true })
              context.bool holds
          end)
        requires;
      Constants.write_output st output);
  finish_instance st ~rest:[] ()

let call_evaluation context (key : Instance.key) ~function_ ~arguments : Emit_c.Builder.instance =
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
      let output = Constants.begin_output st in
      Glue.encode_call context.glue st.builder
        ~output:(Address { place = output; writable = true })
        result_ty result;
      Constants.write_output st output);
  finish_instance st ~rest:[] ()

(* Lowers a function or a test that has a body in source. *)
let source_code context key ~path ~type_arguments : Emit_c.Builder.instance =
  let code = code_of context path type_arguments in
  let body = (Mir_form.mir_of context path).body in
  let st = enter context ~builder:(create context.env ~key) (frame_of code ~inlined:[ path ]) in
  let convention, returns = result_of context code.substitution code.result in
  result_slot st convention;
  let parameter_locals, places = begin_body st ~body in
  Mir_form.lower_code st path ~parameters:places;
  finish_instance st ~returns ~rest:parameter_locals ()

let instance context (key : Instance.key) : Emit_c.Builder.instance =
  match key with
  | Entry method_key -> entry context key method_key
  | Any_entry method_key -> any_entry context key method_key
  | Locked_entry { capability; name } -> Generated.locked_entry context key ~capability ~name
  | Adapter { function_; ty } -> adapter context key ~function_ ~ty
  | Program_main main -> program_main context key main
  | Code { path; type_arguments } -> source_code context key ~path ~type_arguments
  | _ -> bug "%s is not code from source" (Instance.to_string key)

module For_testing = struct
  let constant_value = constant_value
end
