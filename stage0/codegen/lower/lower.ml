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
  evaluate : (Path.t -> Ground.ty -> Lir.static_value) ref;
}

let context = Definitions.context
let test_key = Definitions.test_key
let cursor_result = Targets.cursor_result
let constant = Constants.constant
let evaluator = Constants.evaluator
let table = Generated.table
let any_table = Generated.any_table
let real_evidence = Generated.real_evidence

let trait_provides context ~trait ~name ~receiver =
  match demand context Names.definition (key_of context trait) with
  | Some { kind = Trait { members; _ }; _ } ->
      List.exists
        (fun (member : S.trait_member S.line) ->
          match member.kind with
          | Trait_method { signature; body = Some _ } ->
              name_of signature = name && receiver_of signature.parameters = receiver
          | _ -> false)
        members
  | _ -> false

(* Binds the parameters of the code being lowered, each as [how] passes it,
   and has the function's scope own each [own] one. Gives each one's local,
   if it has one, with its mode and type. *)
let bind_parameters ?how st =
  List.map
    (fun (mode, ty, (written : S.parameter)) ->
      let ty = ground st ty in
      let arrives, place = parameter st ?how (Monomorphic.mode mode) ty in
      (match written.kind with
      | Self_parameter _ -> st.frame.self_place <- Some place
      | Named_parameter { name; _ } -> Hashtbl.replace st.frame.bindings name.id place
      | Parameter_error -> ());
      if mode = T.Own && not (trivial st ty) then own_in_scope st place;
      (arrives, mode, ty))
    st.frame.code.parameter_types

(* The start every function from source shares, after its result's slot:
   its parameters, the mask of defaults passed, and the evidence it is
   given, with its defaults filled in and its [requires] clauses checked.
   Gives the parameters bound, and every parameter's local in order. *)
let begin_body ?how st =
  let code = st.frame.code in
  let bound = bind_parameters ?how st in
  let mask =
    if code.has_defaults then Some (local st.b ~name:"passed" (Raw (Integer UInt64))) else None
  in
  let evidence = evidence_parameters st (evidence_for code.substitution code.uses) in
  st.evidence <-
    st.evidence @ Generated.real_evidence_of st.context ~user:(Path.show code.anchor) code.real;
  start st.b (block st.b);
  Option.iter (fill_defaults st) mask;
  check_requires st;
  (bound, List.filter_map (fun (arrives, _, _) -> arrives) bound @ Option.to_list mask @ evidence)

(* The pulled version of a yielding method: lowered as the method is, but
   holding its arguments as a cursor does, and with its own [yield]s left
   for yield lowering. *)
let pulled context (yielding : Ground.yielding) : Lir.function_ * Lir.local list =
  let code = code_of context yielding.method_ yielding.type_arguments in
  let st = enter context ~pulling:true (frame_of code ~inlined:[ yielding.method_ ]) in
  let bound, parameters = begin_body st ~how:(Convention.held context.env) in
  let owned =
    List.filter_map
      (fun (arrives, mode, ty) -> if mode = T.Own && not (trivial st ty) then arrives else None)
      bound
  in
  block_into st code.body None;
  (finish_function st ~first:[] ~rest:parameters (), owned)

(* Code run while compiling, for a tagged template's check: a template of
   the literal texts and no parts, given to the tag's [from_template]'s
   clauses that can run, each worked out and written out as a [Bool], in
   order. A clause that reads the template's parts is not asked of it; the
   prover asks only those that read its literals. *)
let check_state context from_template =
  let code = code_of context from_template [] in
  (enter context (frame_of code ~inlined:[ from_template ]), code)

(* The positions, among a tag's [from_template]'s clauses, of those a
   template check works out. *)
let template_checked context from_template =
  let st, code = check_state context from_template in
  List.concat
    (List.mapi (fun index clause -> if executable st clause then [ index ] else []) code.requires)

let template_check context (key : Instance.key) ~from_template ~texts : Lir.t =
  let st, code = check_state context from_template in
  start st.b (block st.b);
  in_scope st (fun () ->
      (match code.parameter_types with
      | [ (_, ty, (parameter : S.parameter)) ] -> (
          let ty = ground st ty in
          let built = Values.template_value st ty texts ~span:code.body.span ~parts:[] in
          if not (trivial st ty) then own_in_scope st built;
          match parameter.kind with
          | Named_parameter { name; _ } -> Hashtbl.replace st.frame.bindings name.id built
          | _ -> bug "a from_template without a named parameter")
      | _ -> bug "from_template takes one template");
      Constants.begin_output st;
      List.iter
        (fun clause ->
          if executable st clause then begin
            let holds = new_local st context.bool in
            into st clause holds;
            Glue.encode_call context.glue st.b context.bool holds
          end)
        code.requires;
      Constants.write_output st);
  { key; main = finish_function st ~first:[] ~rest:[] (); nested = nested_functions st }

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
  | Code { path; type_arguments } ->
      let code = code_of context path type_arguments in
      let st = enter context (frame_of code ~inlined:[ path ]) in
      let convention, returns = result_of context code.substitution code.result in
      result_slot st convention;
      let _, parameters = begin_body st in
      block_into st code.body (result_place st);
      {
        key;
        main = finish_function st ~returns ~first:[] ~rest:parameters ();
        nested = nested_functions st;
      }
  | _ -> bug "%s is not code from source" (Instance.to_string key)
