(* Lowering: the checked form of one instance to its LIR. The library's
   modules, in the order each builds on the ones before it:

   - [Definitions]: lowering's context, and finding an instance's code and
     signature
   - [Lowering]: the state of lowering one function, its scopes, locals,
     and positions
   - [Targets]: what a call reaches, how arguments are passed, evidence,
     and literals
   - [Forward]: references that let the parts below call one another
   - [Matching]: testing and binding patterns
   - [Calls]: arguments, inlining, calls, defaults, and [requires] checks
   - [Values]: literals, templates, collections, [provide], [?], lambdas,
     [with], interpolation, and [any]
   - [Expressions]: places and values of expressions
   - [Statements]: blocks, statements, loops, conditions, and [match]
   - [Constants], [Derived], [Generated]: constants and their evaluators,
     derived implementations, and the instances lowering makes, such as
     capability tables and the program's [main]
   - this module: pulled methods, each instance, and the interface *)

open Lir_builder
open Definitions
open Lowering
open Targets
open Calls
open Derived
open Generated

(* The knot: each forward reference, which the earlier parts of lowering
   call through, set to the part that defines it. *)
let () =
  Forward.expression := Expressions.expression;
  Forward.into := Expressions.into;
  Forward.operand := Expressions.operand;
  Forward.operator := Expressions.operator;
  Forward.place_expression := Expressions.place_expression;
  Forward.block_into := Statements.block_into;
  Forward.branch := Statements.branch;
  Forward.if_ := Statements.if_;
  Forward.match_ := Statements.match_;
  Forward.statement := Statements.statement

type context = Definitions.context = {
  database : Query.context;
  env : Memory_layout.env;
  glue : Glue.t;
  monomorphic : Monomorphic.context;
  types : Intrinsics.types;
  bool : Ground.ty;
  cursor_fields : (Ground.yielding -> (string * Memory_layout.member) list) ref;
  checks : bool;
  constant : (Path.t -> Lir.static_value option) ref;
}

let context = Definitions.context
let test_key = Definitions.test_key
let cursor_result = Targets.cursor_result

type constant = Constants.constant = Folded of Lir.data | Run of Ground.ty

let constant = Constants.constant
let evaluator = Constants.evaluator
let table = Generated.table
let any_table = Generated.any_table

let trait_provides context ~trait ~name ~receiver =
  written context (Method { owner = trait; name; receiver }) <> None

(* Binds the parameters of the code being lowered, each as [how] passes it.
   The function owns each [own] one, apart from one with a default, which
   may arrive holding nothing: [fill_defaults] gives that one an owner.
   Gives each one's local, if it has one, with its mode, its type, and for
   one with a default, its bit in the mask of defaults passed. *)
let bind_parameters ?how st =
  let defaults = ref 0 in
  List.map
    (fun (mode, ty, (written : S.parameter)) ->
      let ty = ground st ty in
      let bit =
        match written.kind with
        | Named_parameter { default = Some _; _ } ->
            incr defaults;
            Some (!defaults - 1)
        | _ -> None
      in
      let arrives, place =
        parameter st ?how ~owned:(mode = T.Own && bit = None) (Monomorphic.mode mode) ty
      in
      (match written.kind with
      | Self_parameter _ -> st.frame.self_place <- Some place
      | Named_parameter { name; _ } -> Hashtbl.replace st.frame.bindings name.id place
      | Parameter_error -> ());
      (arrives, mode, ty, bit))
    st.frame.code.parameter_types

(* The start every function from source shares, after its result's slot:
   its parameters, the mask of defaults passed, and the evidence it is
   given, with its defaults filled in and its [requires] clauses checked.
   Gives the parameters bound, the mask, and every parameter's local in
   order. *)
let begin_body ?how st =
  let code = st.frame.code in
  let bound = bind_parameters ?how st in
  let mask =
    if code.has_defaults then Some (local st.b ~name:"passed" (Raw (Integer UInt64))) else None
  in
  let evidence = evidence_parameters st (evidence_for code.substitution code.uses) in
  start st.b (block st.b);
  st.evidence <-
    st.evidence @ Generated.real_implementations st ~user:(Path.show code.anchor) code.real;
  Option.iter (fill_defaults st) mask;
  check_requires st;
  ( bound,
    mask,
    List.filter_map (fun (arrives, _, _, _) -> arrives) bound @ Option.to_list mask @ evidence )

(* The pulled version of a yielding method: lowered as the method is, but
   holding its arguments as a cursor does, and with its own [yield]s left
   for yield lowering. With it, what a cursor that has not started owns:
   each [own] argument's local, and for a parameter with a default, the
   mask's local and the parameter's bit in it, since the argument is there
   only when the bit is set. *)
let pulled context (yielding : Ground.yielding) :
    Lir.function_ * (Lir.local * (Lir.local * int) option) list =
  let code = code_of context yielding.method_ yielding.type_arguments in
  let st = enter context ~pulling:true (frame_of code ~inlined:[ yielding.method_ ]) in
  let bound, mask, parameters = begin_body st ~how:(Convention.held context.env) in
  let owned =
    List.filter_map
      (fun (arrives, mode, ty, bit) ->
        if mode = T.Own && not (trivial st ty) then
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
  block_into st code.body None;
  (finish_function st ~first:[] ~rest:parameters (), owned)

(* Code run while compiling, for a tagged template's check: a template of
   the literal texts and no parts, given to the tag's [from_template]'s
   clauses that can run, each worked out and written out as a [Bool], in
   order. A clause that reads the template's parts is not asked of it; the
   prover asks only those that read its literals. *)
let code_state context path =
  let code = code_of context path [] in
  (enter context (frame_of code ~inlined:[ path ]), code)

(* The positions, among a tag's [from_template]'s clauses, of those a
   template check works out. *)
let template_checked context from_template =
  let st, code = code_state context from_template in
  List.concat
    (List.mapi (fun index clause -> if executable st clause then [ index ] else []) code.requires)

let template_check context (key : Instance.key) ~from_template ~texts : Lir.t =
  let st, code = code_state context from_template in
  start st.b (block st.b);
  in_scope st (fun () ->
      (match code.parameter_types with
      | [ (_, ty, (parameter : S.parameter)) ] -> (
          let ty = ground st ty in
          let built = Values.template_value st ty texts ~span:code.body.span ~parts:[] in
          match parameter.kind with
          | Named_parameter { name; _ } -> Hashtbl.replace st.frame.bindings name.id built
          | _ -> bug "a from_template without a named parameter")
      | _ -> bug "from_template takes one template");
      let output = Constants.begin_output st in
      List.iter
        (fun clause ->
          if executable st clause then begin
            let holds = temporary st context.bool in
            into st clause holds;
            Glue.encode_call context.glue st.b
              ~output:(Address { place = output; writable = true })
              context.bool holds
          end)
        code.requires;
      Constants.write_output st output);
  { key; main = finish_function st ~first:[] ~rest:[] (); nested = nested_functions st }

(* Code run while compiling, for a call whose arguments are known: the
   function, which is not generic, called with each argument a constant,
   and its result written out. *)
let call_evaluation context (key : Instance.key) ~function_ ~arguments : Lir.t =
  let st, _ = code_state context function_ in
  start st.b (block st.b);
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
            emit st.b (Assign (place, Use constant));
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
        ~signature ~substitution:[] ~arguments:passed ~mask:0 ~destination:result;
      let output = Constants.begin_output st in
      Glue.encode_call context.glue st.b
        ~output:(Address { place = output; writable = true })
        result_ty result;
      Constants.write_output st output);
  { key; main = finish_function st ~first:[] ~rest:[] (); nested = nested_functions st }

(* Lowers a function or a test that has a body in source. The body is
   lowered from its core form where [Core_form] handles every node in it,
   and from the syntax tree otherwise. Also returns the reason for the
   fallback to the syntax tree, if there was one. *)
let source_code context key ~path ~type_arguments : Lir.t * string option =
  let code = code_of context path type_arguments in
  (* Lowers the function with [body] lowering its body, or returns the error
     that [body] returns. *)
  let lowered body : (Lir.t, string) result =
    let st = enter context (frame_of code ~inlined:[ path ]) in
    let convention, returns = result_of context code.substitution code.result in
    result_slot st convention;
    let _, _, parameters = begin_body st in
    Result.map
      (fun () : Lir.t ->
        {
          key;
          main = finish_function st ~returns ~first:[] ~rest:parameters ();
          nested = nested_functions st;
        })
      (body st)
  in
  let from_core =
    match demand context Infer.core_of_path path with
    | Some (form, _) -> lowered (fun st -> Core_form.body st form)
    | None -> Error "a definition with no core form"
  in
  match from_core with
  | Ok instance -> (instance, None)
  | Error reason -> (
      match lowered (fun st -> Ok (block_into st code.body (result_place st))) with
      | Ok instance -> (instance, Some reason)
      | Error _ -> bug "a body that was not lowered")

let core_fallback_reason context (key : Instance.key) =
  match key with
  | Code { path; type_arguments } -> snd (source_code context key ~path ~type_arguments)
  | _ -> Some "an instance with no body in source"

let instance context (key : Instance.key) : Lir.t =
  match key with
  | Entry method_key -> entry context key method_key
  | Any_entry method_key -> any_entry context key method_key
  | Adapter { function_; ty } -> adapter context key ~function_ ~ty
  | Program_main main -> program_main context key main
  | Code
      {
        path = Method { owner = Derived { type_ = type_path; trait }; name; receiver };
        type_arguments;
      }
    when not (trait_provides context ~trait ~name ~receiver) ->
      derived context ~key ~type_path ~trait ~name ~type_arguments
  | Code { path; type_arguments } -> fst (source_code context key ~path ~type_arguments)
  | _ -> bug "%s is not code from source" (Instance.to_string key)
