(* Lowering: the core form of one instance to its LIR. *)

open Lir_builder
open Definitions
open Lowering
open Targets
open Generated

type unsupported = Lowering.unsupported = { construct : string; at : Lir.site option }

exception Unsupported = Lowering.Unsupported

type context = Definitions.context

let env (context : context) = context.env
let glue (context : context) = context.glue
let monomorphic (context : context) = context.monomorphic
let constant_value (context : context) = context.constant
let context = Definitions.context
let test_key = Definitions.test_key
let cursor_result = Targets.cursor_result

let pulled_evidence context (yielding : Ground.yielding) (function_ : Lir.function_) =
  let count = List.length (Targets.cursor_evidence context yielding) in
  let first = List.length function_.parameters - count in
  List.filteri (fun position _ -> position >= first) function_.parameters

type constant = Constants.constant = Folded of Lir.data | Run of Ground.ty

let constant = Constants.constant
let evaluator = Constants.evaluator
let table = Generated.table
let locked_table = Generated.locked_table
let any_table = Generated.any_table

(* Binds the parameters of the code being lowered, each as [how] passes it.
   The function owns each [own] one, apart from one with a default, which
   may arrive holding nothing: [fill_defaults] gives that one an owner.
   Gives each one's local, if it has one, with its mode, its type, and for
   one with a default, its bit in the mask of defaults passed. *)
let bind_parameters ?how st (parameters : Core.parameter list) =
  let defaults = ref 0 in
  List.map
    (fun (parameter : Core.parameter) ->
      let ty = ground st parameter.type_ in
      let bit =
        Option.map
          (fun _ ->
            incr defaults;
            !defaults - 1)
          parameter.default
      in
      let arrives, place =
        Lowering.parameter st ?how
          ~owned:(parameter.mode = Own && bit = None)
          (Monomorphic.mode parameter.mode) ty
      in
      Mir_form.bind_core st parameter.local place;
      (arrives, parameter.mode, ty, bit))
    parameters

(* The start every function from source shares, after its result's slot:
   its parameters, the mask of defaults passed, and the evidence it is
   given, with its defaults filled in. Returns the parameters bound, the
   mask, and every parameter's local in order. *)
let begin_body ?how st ~(parameters : Core.parameter list) =
  let code = st.frame.code in
  let bound = bind_parameters ?how st parameters in
  let mask =
    if code.has_defaults then Some (local st.builder ~name:"passed" (Raw (Integer UInt64)))
    else None
  in
  let evidence = evidence_parameters st (evidence_for st.context code.substitution code.uses) in
  start st.builder (block st.builder);
  st.evidence <-
    st.evidence @ Generated.real_implementations st ~user:(Path.show code.anchor) code.real;
  Option.iter (fun mask -> Mir_form.fill_defaults st mask parameters) mask;
  ( bound,
    mask,
    List.filter_map (fun (arrives, _, _, _) -> arrives) bound @ Option.to_list mask @ evidence )

(* The pulled version of a yielding method: lowered as the method is, but
   holding its arguments as a cursor does, and with its own [yield]s left
   for yield lowering. With it, the values a cursor that has not started owns:
   each [own] argument's local, and for a parameter with a default, the
   mask's local and the parameter's bit in it, since the argument is there
   only when the bit is set. *)
let pulled context (yielding : Ground.yielding) :
    Lir.function_ * (Lir.local * (Lir.local * int) option) list =
  let code = code_of context yielding.method_ yielding.type_arguments in
  let parameters, _ = Mir_form.core_of context yielding.method_ in
  let st = enter context ~pulling:true (frame_of code ~inlined:[ yielding.method_ ]) in
  let bound, mask, parameter_locals =
    begin_body st ~how:(Convention.held context.env) ~parameters
  in
  let owned =
    List.filter_map
      (fun (arrives, mode, ty, bit) ->
        if mode = Types.Own && not (trivial st ty) then
          Option.map
            (fun local ->
              ( local,
                Option.map
                  (fun bit ->
                    match mask with
                    | Some mask -> (mask, bit)
                    | None -> bug "a default with no mask")
                  bit ))
            arrives
        else None)
      bound
  in
  Mir_form.lower_code st yielding.method_;
  (finish_function st ~first:[] ~rest:parameter_locals (), owned)

let code_state context path =
  let code = code_of context path [] in
  (enter context (frame_of code ~inlined:[ path ]), code)

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

let template_check context (key : Instance.key) ~from_template ~texts : Lir.t =
  let st, _ = code_state context from_template in
  let parameter, requires = from_template_contract context from_template in
  start st.builder (block st.builder);
  in_scope st (fun () ->
      let template =
        template_value st (ground st parameter.type_) texts
          ~site:{ definition = st.frame.code.anchor; line = 1; column = 1 }
          ~parts:[]
      in
      Mir_form.bind_core st parameter.local template;
      let output = Constants.begin_output st in
      List.iter
        (fun (clause : Core.condition) ->
          if clause.executable then begin
            let holds = temporary st context.bool in
            Mir_form.expression_into ~parameters:[ parameter ] st clause.value holds;
            Glue.encode_call context.glue st.builder
              ~output:(Address { place = output; writable = true })
              context.bool holds
          end)
        requires;
      Constants.write_output st output);
  { key; main = finish_function st ~first:[] ~rest:[] (); nested = nested_functions st }

let call_evaluation context (key : Instance.key) ~function_ ~arguments : Lir.t =
  let st, _ = code_state context function_ in
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
              | Bool -> Lir.Constant (Bool (not (Z.equal value Z.zero)))
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
  { key; main = finish_function st ~first:[] ~rest:[] (); nested = nested_functions st }

(* Lowers a function or a test that has a body in source. *)
let source_code context key ~path ~type_arguments : Lir.t =
  let code = code_of context path type_arguments in
  let parameters, _ = Mir_form.core_of context path in
  let st = enter context (frame_of code ~inlined:[ path ]) in
  let convention, returns = result_of context code.substitution code.result in
  result_slot st convention;
  let _, _, parameter_locals = begin_body st ~parameters in
  Mir_form.lower_code st path;
  {
    key;
    main = finish_function st ~returns ~first:[] ~rest:parameter_locals ();
    nested = nested_functions st;
  }

let instance context (key : Instance.key) : Lir.t =
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
