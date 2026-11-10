(* Lowering: the checked form of one instance to its LIR. See CODEGEN.md,
   "Lowering expressions". The library's modules, in the order each builds
   on the ones before it:

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
  database : Query.database;
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

(* The pulled version of a yielding method: lowered as the method is, but
   with its own [yield]s left for yield lowering, and its parameters first
   among its locals, which is how a cursor's fields are named. *)
let pulled context (yielding : Ground.yielding) : Lir.function_ * Lir.local list =
  let code = code_of context yielding.method_ yielding.type_arguments in
  let b = Lir_builder.create () in
  let st =
    {
      context;
      frame =
        {
          code;
          bindings = Hashtbl.create 16;
          self_place = None;
          on_yield = None;
          inlined = [ yielding.method_ ];
          exit = None;
        };
      b;
      scopes = [ { owned = [] } ];
      loops = [];
      temporaries = [];
      return_ = None;
      result_local = None;
      nested = ref [];
      evidence = [];
      pulling = true;
    }
  in
  let owned = ref [] in
  let parameters =
    List.filter_map
      (fun (mode, ty, (parameter : S.parameter)) ->
        let ty = Monomorphic.ground context.monomorphic code.substitution ty in
        let place, local =
          match held context mode ty with
          | None -> (new_local st ty, None)
          | Some (Pointer _ as pointer) ->
              let local = local b pointer in
              ({ Lir.root = Local local; projections = [ Deref ] }, Some local)
          | Some lir_ty ->
              let local = local b lir_ty in
              (at local, Some local)
        in
        (match parameter.kind with
        | Self_parameter _ -> st.frame.self_place <- Some place
        | Named_parameter { name; _ } -> Hashtbl.replace st.frame.bindings name.id place
        | Parameter_error -> ());
        if mode = T.Own && not (Glue.trivial context.glue ty) then begin
          own_in_scope st place;
          Option.iter (fun l -> owned := l :: !owned) local
        end;
        local)
      code.parameter_types
  in
  let mask =
    if code.has_defaults then Some (local b ~name:"passed" (Raw (Integer UInt64))) else None
  in
  let evidence =
    List.map
      (fun capability -> (capability, local b ~name:"evidence" Convention.evidence))
      (evidence_for code.substitution code.uses)
  in
  st.evidence <- List.map (fun (capability, l) -> (capability, Lir.Copy (at l))) evidence;
  start b (block b);
  Option.iter (fill_defaults st) mask;
  check_requires st;
  block_into st code.body None;
  drop_scope st (List.hd st.scopes);
  finish b (Return None);
  ( Lir_builder.build b
      ~parameters:(parameters @ Option.to_list mask @ List.map snd evidence)
      ~result:None,
    List.rev !owned )

(* Code run while compiling, for a tagged template's check: a template of
   the literal texts and no parts, given to the tag's [from_template]'s
   clauses that can run, each worked out and written out as a [Bool], in
   order. A clause that reads the template's parts is not asked of it; the
   prover asks only those that read its literals. See CODEGEN.md, "Code run
   while compiling". *)
let check_state context from_template =
  let code = code_of context from_template [] in
  let st =
    {
      context;
      frame =
        {
          code;
          bindings = Hashtbl.create 4;
          self_place = None;
          on_yield = None;
          inlined = [ from_template ];
          exit = None;
        };
      b = Lir_builder.create ();
      scopes = [ { owned = [] } ];
      loops = [];
      temporaries = [];
      return_ = None;
      result_local = None;
      nested = ref [];
      evidence = [];
      pulling = false;
    }
  in
  (st, code)

(* The positions, among a tag's [from_template]'s clauses, of those a
   template check works out. *)
let template_checked context from_template =
  let st, code = check_state context from_template in
  List.concat
    (List.mapi (fun index clause -> if executable st clause then [ index ] else []) code.requires)

let template_check context (key : Instance.key) ~from_template ~texts : Lir.t =
  let st, code = check_state context from_template in
  let b = st.b in
  start b (block b);
  let call ?result intrinsic arguments =
    emit b
      (Call
         {
           target = Intrinsic intrinsic;
           arguments;
           result = (match result with Some r -> Lir.Returned r | None -> Discarded);
         })
  in
  in_scope st (fun () ->
      (match code.parameter_types with
      | [ (_, ty, (parameter : S.parameter)) ] -> (
          let ty = Monomorphic.ground context.monomorphic code.substitution ty in
          let built = Values.template_value st ty texts ~span:code.body.span ~parts:[] in
          if not (trivial st ty) then own_in_scope st built;
          match parameter.kind with
          | Named_parameter { name; _ } -> Hashtbl.replace st.frame.bindings name.id built
          | _ -> bug "a from_template without a named parameter")
      | _ -> bug "from_template takes one template");
      call Debug_begin [];
      List.iter
        (fun clause ->
          if executable st clause then begin
            let holds = new_local st context.bool in
            into st clause holds;
            Glue.encode_call context.glue b context.bool holds
          end)
        code.requires;
      let bytes = local b (Raw (Pointer Opaque)) and length = new_local st context.types.usize in
      call ~result:(at bytes) Debug_bytes [];
      call ~result:length Debug_length [];
      let written = new_local st context.types.isize in
      call ~result:written System_write
        [ Constant (Integer (Int32, Z.one)); Copy (at bytes); Copy length ]);
  finish b (Return None);
  {
    key;
    main = Lir_builder.build b ~parameters:[] ~result:None;
    nested =
      Array.of_list
        (List.map (function Some f -> f | None -> bug "a lambda left unfinished") !(st.nested));
  }

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
      let b = Lir_builder.create () in
      let lir_signature, result =
        lir_signature context code.substitution
          ~parameters:(List.map (fun (mode, ty, _) -> (mode, ty)) code.parameter_types)
          ~has_defaults:code.has_defaults code.result
      in
      ignore lir_signature;
      let return_pointer =
        match result with
        | Through_pointer pointer -> Some (local b ~name:"result" pointer)
        | _ -> None
      in
      let st =
        {
          context;
          frame =
            {
              code;
              bindings = Hashtbl.create 16;
              self_place = None;
              on_yield = None;
              inlined = [ path ];
              exit = None;
            };
          b;
          scopes = [ { owned = [] } ];
          loops = [];
          temporaries = [];
          return_ =
            Option.map
              (fun pointer -> { Lir.root = Local pointer; projections = [ Deref ] })
              return_pointer;
          result_local = None;
          nested = ref [];
          evidence = [];
          pulling = false;
        }
      in
      let parameters =
        List.filter_map
          (fun (mode, ty, (parameter : S.parameter)) ->
            let ty = Monomorphic.ground context.monomorphic code.substitution ty in
            let place, local =
              match Convention.parameter context.env (Monomorphic.mode mode) ty with
              | None -> (new_local st ty, None)
              | Some (Pointer _ as pointer) ->
                  let local = local b pointer in
                  ({ Lir.root = Local local; projections = [ Deref ] }, Some local)
              | Some lir_ty ->
                  let local = local b lir_ty in
                  (at local, Some local)
            in
            (match parameter.kind with
            | Self_parameter _ -> st.frame.self_place <- Some place
            | Named_parameter { name; _ } -> Hashtbl.replace st.frame.bindings name.id place
            | Parameter_error -> ());
            if mode = Own && not (Glue.trivial context.glue ty) then own_in_scope st place;
            local)
          code.parameter_types
      in
      let mask =
        if code.has_defaults then Some (local b ~name:"passed" (Raw (Integer UInt64))) else None
      in
      let evidence =
        List.map
          (fun capability -> (capability, local b ~name:"evidence" Convention.evidence))
          (evidence_for code.substitution code.uses)
      in
      let result_local =
        match result with
        | Returned ty -> Some (local b ~name:"result" ty)
        | Nothing | Through_pointer _ -> None
      in
      let st = { st with result_local } in
      st.evidence <-
        List.map (fun (capability, local) -> (capability, Lir.Copy (at local))) evidence;
      start b (block b);
      Option.iter (fill_defaults st) mask;
      let destination =
        match (st.return_, result_local) with
        | Some pointer, _ -> Some pointer
        | None, Some local -> Some (at local)
        | None, None -> None
      in
      check_requires st;
      block_into st code.body destination;
      drop_scope st (List.hd st.scopes);
      finish b
        (match code.result with
        | Returns Never -> Unreachable
        | _ -> Return (Option.map (fun local -> Lir.Move (at local)) result_local));
      let main =
        Lir_builder.build b ?written_result:return_pointer
          ~parameters:
            (Option.to_list return_pointer @ parameters @ Option.to_list mask
           @ List.map snd evidence)
          ~result:(match result with Returned ty -> Some ty | _ -> None)
      in
      {
        key;
        main = { main with returns = code.result <> Returns Never };
        nested =
          Array.of_list
            (List.map
               (function Some f -> f | None -> bug "a lambda left unfinished")
               !(st.nested));
      }
  | _ -> bug "%s is not code from source" (Instance.to_string key)
