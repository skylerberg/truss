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

let bind_parameters ?cursor st (body : Mir.body) =
  let defaults = ref 0 and held = ref 0 in
  let bound =
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
          match cursor with
          | None ->
              Lowering.parameter st ~in_scope:false
                ~owned:(mode = Own && bit = None)
                (Monomorphic.mode mode) ty
          | Some cursor -> (
              match Convention.held st.context.env (Monomorphic.mode mode) ty with
              | None -> (None, temporary st ty)
              | Some ty -> (
                  let field = cursor_field cursor (Convention.cursor_parameter !held) ty in
                  incr held;
                  (None, match ty with Pointer _ -> field / Deref | _ -> field)))
        in
        (arrives, mode, ty, bit, place))
      body.parameters
  in
  (bound, !held)

let begin_body st ~(body : Mir.body) =
  let code = st.frame.code in
  let bound, _ = bind_parameters st body in
  let places = List.map (fun (_, _, _, _, place) -> place) bound in
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
  ( List.filter_map (fun (arrives, _, _, _, _) -> arrives) bound @ Option.to_list mask @ evidence,
    places )

type pulled = {
  next : Emit_c.fragment;
  drop : Emit_c.fragment;
  fields : (string * Memory_layout.member) list;
}

let member : Lowered.ty -> Memory_layout.member = function
  | Value ty -> Typed ty
  | Raw scalar -> Raw scalar
  | Pointer { target = Value ty; _ } -> Raw (Pointer (Data ty))
  | Pointer _ | Environment _ | Evidence _ -> bug "a value a cursor cannot hold"

let pulled context (yielding : Ground.yielding) : pulled =
  let code = code_of context yielding.method_ yielding.type_arguments in
  let body = (Mir_form.mir_of context yielding.method_).body in
  let st =
    enter context
      ~builder:(create context.env ~key:(Cursor_next yielding))
      (frame_of code ~inlined:[ yielding.method_ ])
  in
  (* [next] starts in block 0, which builds the evidence the method's code
     reads on every call, then goes to the state's code. *)
  let entry = block st.builder in
  result_slot st (Convention.result context.env (cursor_result context yielding));
  let pointer =
    local st.builder ~name:"cursor" (Pointer { target = Value (Cursor yielding); writable = true })
  in
  let cursor =
    {
      pointer;
      drop = Emit_c.Builder.separate st.builder ~key:(Drop (Cursor yielding)) ~parts:[ pointer ];
      fields = ref [];
      resumes = [];
      stops = [];
    }
  in
  describe_cursor st.builder yielding cursor.fields;
  let st = { st with cursor = Some cursor } in
  let bound, held = bind_parameters ~cursor st body in
  let mask =
    if code.has_defaults then
      Some (cursor_field cursor (Convention.cursor_parameter held) (Raw (Integer UInt64)))
    else None
  in
  let evidence = evidence_parameters st (evidence_for st.context code.substitution code.uses) in
  start st.builder entry;
  st.evidence <-
    st.evidence @ Generated.real_implementations st ~user:(Path.show code.anchor) code.real;
  let dispatch = block st.builder and first = block st.builder in
  finish st.builder (Goto dispatch);
  start st.builder first;
  let places = List.map (fun (_, _, _, _, place) -> place) bound in
  let places =
    match mask with Some mask -> Mir_form.fill_defaults st mask body places | None -> places
  in
  Mir_form.lower_code st yielding.method_ ~parameters:places;
  let state = Mir_form.cursor_state cursor in
  let switch ~started ~ended blocks =
    finish st.builder
      (Switch
         {
           value = Copy state;
           cases =
             [ (Z.zero, started); (Z.one, ended) ]
             @ List.mapi (fun index block -> (Z.of_int (index + 2), block)) (List.rev blocks);
           default = None;
         })
  in
  let ended = block st.builder in
  in_block st.builder ended (fun () -> Mir_form.give_option st None);
  in_block st.builder dispatch (fun () -> switch ~started:first ~ended cursor.resumes);
  Emit_c.Builder.write_in st.builder cursor.drop (fun () ->
      let unstarted = block st.builder and ended = block st.builder in
      start st.builder unstarted;
      List.iter
        (fun (_, mode, ty, bit, place) ->
          if mode = Types.Own && not (trivial st ty) then
            match (bit, mask) with
            | None, _ -> emit st.builder (Drop place)
            | Some bit, Some mask ->
                let bits = local st.builder (Raw (Integer UInt64))
                and passed = local st.builder (Raw Bool) in
                emit st.builder
                  (Assign
                     ( at bits,
                       Binary (Bit_and, Copy mask, constant_int UInt64 (Z.shift_left Z.one bit)) ));
                emit st.builder
                  (Assign (at passed, Binary (Not_equal, Copy (at bits), constant_int UInt64 Z.zero)));
                when_ st.builder (Copy (at passed)) (fun () -> emit st.builder (Drop place))
            | Some _, None -> bug "a default with no mask")
        bound;
      finish st.builder (Return None);
      start st.builder ended;
      finish st.builder (Return None);
      start st.builder (Emit_c.Builder.separate_entry st.builder cursor.drop);
      switch ~started:unstarted ~ended cursor.stops);
  finish_function st ~first:[] ~rest:(pointer :: evidence) ();
  {
    next = Emit_c.fragment context.env (Code (built st.builder));
    drop = Emit_c.fragment context.env (Code (built_separate st.builder cursor.drop));
    fields =
      (Convention.cursor_state, Memory_layout.Raw (Integer UInt32))
      :: List.rev_map (fun (name, ty) -> (name, member ty)) !(cursor.fields);
  }

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
