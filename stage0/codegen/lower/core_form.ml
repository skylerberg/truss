(* Lowers a function body from its core form.

   The core form records what the type checker resolved: the callee of each
   call, whether each operand is a place or a value, and every type. So this
   lowering does no name resolution and no type inference. A body with a
   node kind that is not handled yet raises [Unhandled_node], and the caller
   lowers that body from the syntax tree instead. *)

open Definitions
open Lowering
open Targets
open Lir_builder

(* A node kind that this lowering does not handle yet, with a description of
   the kind. *)
exception Unhandled_node of string

let unhandled what = raise (Unhandled_node what)

let spans st =
  match demand st.context Names.spans st.frame.code.definition_key with
  | Some spans -> spans
  | None -> bug "no spans for %s" (Path.show st.frame.code.anchor)

(* The source position of a node, for a failure message. *)
let site_of st (origin : Core.origin) = site st (spans st).(origin)

let local_place st (local : Core.local) : Lir.place =
  let bound = function Some place -> place | None -> bug "a local with no place" in
  match local with
  | Named id -> bound (Hashtbl.find_opt st.frame.bindings id)
  | Self -> bound st.frame.self_place
  | Synthetic number -> bound (Hashtbl.find_opt st.frame.synthetic number)

let bind_local st (local : Core.local) place =
  match local with
  | Named id -> Hashtbl.replace st.frame.bindings id place
  | Synthetic number -> Hashtbl.replace st.frame.synthetic number place
  | Self -> bug "a pattern that binds self"

(* Descriptions of the node kinds that are not handled yet. *)
let expression_kind : Core.kind -> string = function
  | Interpolated _ -> "an interpolated string"
  | Template _ -> "a tagged string"
  | Copy _ -> "a copy"
  | Function_value _ -> "a function as a value"
  | Value_parameter _ -> "a generic value parameter"
  | Lambda _ -> "a lambda"
  | Collection_literal _ | Map_literal _ -> "a collection literal"
  | Record_update _ -> "a record update"
  | Slice _ -> "a slice"
  | Cursor_next _ -> "a cursor's next value"
  | Convert _ -> "a conversion"
  | To_any _ -> "a conversion to an any value"
  | Provide _ -> "a provide"
  | _ -> "a specification-only expression"

let statement_kind : Core.statement_kind -> string = function
  | Parallel _ -> "a parallel block"
  | Yield _ -> "a yield"
  | Evaluate _ | Let _ | Assign _ | Compound_assign _ | Assert _ | For _ | While _ | Proof _ ->
      "a statement"

let binary : Core.comparison -> Lir.binary = function
  | Equal -> Equal
  | Not_equal -> Not_equal
  | Less -> Less
  | Less_equal -> Less_equal
  | Greater -> Greater
  | Greater_equal -> Greater_equal

let evidence : Core.evidence -> C.evidence = function
  | Impl { impl; arguments } -> Impl { impl; arguments }
  | Bound -> Bound
  | Dynamic -> unhandled "a call through an any value"

(* Patterns *)

let rec binds_name (pattern : Core.pattern) =
  match pattern.kind with
  | Bind _ -> true
  | Variant { fields; _ } | Record fields -> List.exists (fun (_, inner) -> binds_name inner) fields
  | Alternatives alternatives -> List.exists binds_name alternatives
  | Wildcard | Literal _ | Range _ | Equal_to _ -> false

(* Every list that takes one element from each of the lists, in order. *)
let rec product = function
  | [] -> [ [] ]
  | choices :: rest ->
      let rest = product rest in
      List.concat_map (fun choice -> List.map (fun chosen -> choice :: chosen) rest) choices

(* The patterns that one pattern stands for once each alternative that binds
   a name is a pattern of its own: [Circle(radius: n) | Square(side: n)] is
   two patterns. A name is bound from the part that its own alternative
   matched, so alternatives that bind are tested and bound separately.
   Alternatives that bind nothing stay as they are. *)
let rec expand_alternatives (pattern : Core.pattern) : Core.pattern list =
  let expand_fields fields =
    product
      (List.map
         (fun (field, inner) -> List.map (fun inner -> (field, inner)) (expand_alternatives inner))
         fields)
  in
  match pattern.kind with
  | Alternatives alternatives when binds_name pattern ->
      List.concat_map expand_alternatives alternatives
  | Variant { variant; fields } ->
      List.map
        (fun fields -> { pattern with kind = Variant { variant; fields } })
        (expand_fields fields)
  | Record fields ->
      List.map (fun fields -> { pattern with kind = Record fields }) (expand_fields fields)
  | Wildcard | Bind _ | Literal _ | Range _ | Equal_to _ | Alternatives _ -> [ pattern ]

(* A name that a pattern binds, with the place of the part it matched. *)
type bound_name = {
  local : Core.local;
  name : string;
  mode : T.mode;
  ty : Ground.ty;
  part : Lir.place;
}

(* Where a name's value is kept when several patterns share the code that
   follows them: in a local of its own, or behind a pointer to the part. *)
type slot = Value_slot of Lir.place | Pointer_slot of Lir.local

(* Whether a name gets a local of its own: it owns the part, or the part
   copies implicitly and the name does not change it. Otherwise the name
   aliases the part. *)
let has_own_local st (bound : bound_name) =
  bound.mode = Own || (trivial st bound.ty && bound.mode <> Mut)

let rec bound_names st (pattern : Core.pattern) (place : Lir.place) : bound_name list =
  match pattern.kind with
  | Bind { local; name; mode; _ } ->
      [ { local; name; mode; ty = ground st pattern.type_; part = place } ]
  | Variant { variant; fields } ->
      List.concat_map
        (fun (field, inner) -> bound_names st inner (place / Variant_field { variant; field }))
        fields
  | Record fields ->
      List.concat_map (fun (field, inner) -> bound_names st inner (place / Field field)) fields
  | Wildcard | Literal _ | Range _ | Equal_to _ | Alternatives _ -> []

(* Binds a name to its part: moved or copied into a local of its own, or as
   an alias of the part. *)
let bind_name st (bound : bound_name) =
  if has_own_local st bound then begin
    let variable = binding st ~name:bound.name bound.ty in
    emit st.b (Assign (variable, Use (owned st bound.part bound.ty)));
    bind_local st bound.local variable
  end
  else bind_local st bound.local bound.part

let rec place st (source : Core.place) : Lir.place =
  match source with
  | Local local -> local_place st local
  | Field { base; field; _ } -> place st base / Field field
  | Temporary value -> value_place st value
  | Lent _ -> unhandled "a place that a call lends"

and operand_place st (operand : Core.operand) : Lir.place =
  match operand with Place source -> place st source | Value value -> value_place st value

(* Evaluates an expression into a new temporary, which lives until the end
   of the statement. *)
and value_place st (value : Core.expression) : Lir.place =
  let ty =
    match value.kind with
    (* These diverge, so the temporary is never read. *)
    | Return _ | Break | Continue -> Monomorphic.builtin Unit
    | _ -> ground st value.type_
  in
  let result = temporary st ty in
  into st value result;
  result

and operand st (value : Core.expression) : Lir.operand =
  match value.kind with
  | Integer number -> constant_of st (ground st value.type_) (Integer_value number)
  | Float number -> constant_of st (ground st value.type_) (Float_value number)
  | Boolean truth -> Constant (Bool truth)
  | _ -> Copy (value_place st value)

(* Evaluates an expression and writes its value to [destination]. *)
and into st (value : Core.expression) (destination : Lir.place) =
  let ty = ground st value.type_ in
  let assign rvalue = emit st.b (Assign (destination, rvalue)) in
  match value.kind with
  | Integer _ | Float _ | Boolean _ -> assign (Use (operand st value))
  | Use source -> take st (place st source) ty ~destination
  | String text -> string_literal st ty text ~destination
  | Constant path -> take st (Matching.static_constant st path) ty ~destination
  | Construct { variant; fields } ->
      let fields =
        List.map
          (fun (name, (field : Core.expression option)) ->
            match field with
            | None -> unhandled "a field left to its default"
            | Some field -> (name, owned st (value_place st field) (ground st field.type_)))
          fields
      in
      assign (Build { ty; variant; fields })
  | Call call -> call_into st value call destination
  | Operator { operation; arguments } ->
      ignore
        (Intrinsics.lower ~checks:st.context.checks st.context.env st.b st.context.types operation
           ~type_arguments:(List.map (fun (a : Core.expression) -> ground st a.type_) arguments)
           (List.map (fun argument -> Intrinsics.Value (operand st argument)) arguments)
           ~destination:(Some destination) ~site:(site_of st value.origin))
  | Compare { comparison; left; right } ->
      assign (Binary (binary comparison, operand st left, operand st right))
  | Not inner -> assign (Unary (Not, operand st inner))
  | And _ | Or _ | Matches _ ->
      (* A condition used as a value: true on the path to [yes], and false
         on the path to [no]. *)
      in_scope st (fun () ->
          let yes = block st.b and no = block st.b and after = block st.b in
          branch st value ~yes ~no;
          start st.b yes;
          assign (Use (Constant (Bool true)));
          finish st.b (Goto after);
          start st.b no;
          assign (Use (Constant (Bool false)));
          finish st.b (Goto after);
          start st.b after)
  | If { condition; then_; else_ } -> if_ st ~condition ~then_ ~else_ (Some destination)
  | Match { scrutinees; arms; _ } -> match_ st ~scrutinees ~arms destination
  | Block inner -> block_into st inner (Some destination)
  | Return returned -> return_ st returned
  | Current_target -> (
      match st.compound_target with
      | Some target -> take st target ty ~destination
      | None -> bug "the current value of a target outside a compound assignment")
  | Break -> (
      match st.loops with
      | loop :: _ ->
          leave_to st loop.break_depth;
          finish st.b (Goto loop.break_);
          start st.b (block st.b)
      | [] -> bug "a break outside a loop")
  | Continue -> (
      match st.loops with
      | loop :: _ ->
          leave_to st loop.continue_depth;
          finish st.b (Goto loop.continue_);
          start st.b (block st.b)
      | [] -> bug "a continue outside a loop")
  | Todo ->
      let message = "todo reached" in
      finish st.b
        (Fail
           {
             failure = Todo;
             message = Constant (Bytes message);
             length = usize (String.length message);
             site = site_of st value.origin;
           });
      start st.b (block st.b)
  | Unreachable -> unreachable_block st
  | Echo inner ->
      into st inner destination;
      Values.echo st destination ty (spans st).(value.origin)
  | kind -> unhandled (expression_kind kind)

(* Evaluates a call's arguments, one for each of the callee's parameters, in
   order. An argument that is a place is passed where it is, and a value is
   evaluated into a temporary. An omitted argument gets an uninitialized
   temporary, which the callee fills with the default. The returned mask has
   one bit for each parameter with a default, set where the call passes an
   argument. *)
and evaluate_arguments st (signature : T.signature) substitution (arguments : Core.argument list) =
  let parameters = interface_parameters signature in
  if List.length parameters <> List.length arguments then
    bug "a call with %d arguments for %d parameters" (List.length arguments)
      (List.length parameters);
  let receivers = List.length parameters - List.length signature.parameters in
  let mask = ref 0 and defaulted = ref 0 in
  let evaluated =
    List.mapi
      (fun index ((mode, ty), (argument : Core.argument)) ->
        let ty = Monomorphic.ground st.context.monomorphic substitution ty in
        let bit =
          if index >= receivers && (List.nth signature.parameters (index - receivers)).has_default
          then begin
            incr defaulted;
            Some (!defaulted - 1)
          end
          else None
        in
        match argument with
        | Default -> (mode, ty, temporary st ty)
        | Passed { value; _ } ->
            Option.iter (fun bit -> mask := !mask lor (1 lsl bit)) bit;
            (mode, ty, operand_place st value))
      (List.combine parameters arguments)
  in
  if !defaulted > 62 then
    Compiler_bug.unsupported "a function with more than 62 parameters that have defaults";
  (evaluated, !mask)

(* The function or method that a callee resolves to in this instance, with
   its type arguments. [None] for a callee that is neither. *)
and resolve_callee st (callee : Core.callee) : (Path.t * Ground.argument list) option =
  match callee with
  | Function { path; type_arguments } ->
      Some
        ( path,
          List.map
            (Monomorphic.ground_argument st.context.monomorphic st.frame.code.substitution)
            type_arguments )
  | Trait_method { trait; name; receiver; self_type; type_arguments; evidence = core_evidence } -> (
      match
        trait_method_key st ~trait ~name ~receiver ~self_type ~type_arguments
          ~evidence:(evidence core_evidence)
      with
      | Code { path; type_arguments } -> Some (path, type_arguments)
      | _ -> bug "a trait method's key")
  | Capability_method _ | Intrinsic _ | Indirect _ -> None

and call_into st (value : Core.expression) (call : Core.call) destination =
  if call.lends <> None then unhandled "a call that lends";
  match (resolve_callee st call.callee, call.callee) with
  | Some (path, type_arguments), _ ->
      let signature = signature_of st.context path in
      (match signature.output with
      | Returns _ -> ()
      | Yields _ | Lends _ -> unhandled "a call of a yielding method outside a loop");
      let substitution = bind signature.generics type_arguments in
      let arguments, mask = evaluate_arguments st signature substitution call.arguments in
      call_instance st
        (Code { path; type_arguments })
        ~signature ~substitution ~arguments ~mask ~destination
  | None, Intrinsic { operation; type_arguments } -> (
      let type_arguments =
        List.filter_map
          (fun argument ->
            match
              Monomorphic.ground_argument st.context.monomorphic st.frame.code.substitution argument
            with
            | Type ty -> Some ty
            | _ -> None)
          type_arguments
      in
      let arguments =
        List.map
          (fun (argument : Core.argument) ->
            match argument with
            | Passed { value = Place source; _ } -> Intrinsics.Place (place st source)
            | Passed { mode; value = Value value } ->
                let ty = ground st value.type_ in
                let evaluated = value_place st value in
                (* An intrinsic takes storage and views by place. *)
                if Storage.elements_of ty <> None || Storage.viewed ty <> None then
                  Intrinsics.Place evaluated
                else
                  Intrinsics.Value (if mode = T.Own then owned st evaluated ty else Copy evaluated)
            | Default -> bug "an intrinsic called with an omitted argument")
          call.arguments
      in
      match
        Intrinsics.lower ~checks:st.context.checks st.context.env st.b st.context.types operation
          ~type_arguments arguments ~destination:(Some destination) ~site:(site_of st value.origin)
      with
      | Some _ -> unhandled "an intrinsic that lends"
      | None -> ())
  | None, Capability_method _ -> unhandled "a call of a capability method"
  | None, _ -> unhandled "a call through a function value"

and return_ st (returned : Core.expression option) =
  (match st.frame.exit with Some _ -> unhandled "a return in an inlined method" | None -> ());
  (match (returned, result_place st) with
  | Some returned, Some result ->
      clear_result st;
      into st returned result
  | Some returned, None -> ignore (value_place st returned)
  | None, _ -> ());
  leave_to st 0;
  finish st.b (return_result st);
  start st.b (block st.b)

and if_ st ~(condition : Core.expression) ~(then_ : Core.block) ~(else_ : Core.block option)
    destination =
  let yes = block st.b and no = block st.b and after = block st.b in
  let scope = open_scope st Bindings in
  branch st condition ~yes ~no;
  start st.b yes;
  block_into st then_ destination;
  close_scope st scope;
  finish st.b (Goto after);
  start st.b no;
  drop_scope st scope;
  Option.iter (fun inner -> block_into st inner destination) else_;
  finish st.b (Goto after);
  start st.b after

(* Lowers a condition to jumps: to [yes] when it is true, and to [no] when it
   is false. *)
and branch st (condition : Core.expression) ~yes ~no =
  match condition.kind with
  | And (left, right) ->
      let middle = block st.b in
      branch st left ~yes:middle ~no;
      start st.b middle;
      branch st right ~yes ~no
  | Or (left, right) ->
      let middle = block st.b in
      branch st left ~yes ~no:middle;
      start st.b middle;
      branch st right ~yes ~no
  | Not inner -> branch st inner ~yes:no ~no:yes
  | Matches { value; pattern } ->
      (* The names that an [is] test binds can alias parts of the tested
         value, so a value that is not a place is stored in the same scope
         as the names. *)
      let scrutinee =
        match value with
        | Place source -> place st source
        | Value value ->
            let kept = binding st (ground st value.type_) in
            into st value kept;
            kept
      in
      match_patterns st [ (pattern, scrutinee) ] ~failed:no;
      finish st.b (Goto yes)
  | _ ->
      let value = operand st condition in
      finish st.b (Switch { value; cases = [ (Z.one, yes) ]; default = Some no })

and block_into st (inner : Core.block) destination =
  in_scope st (fun () ->
      List.iter (statement st) inner.statements;
      match (inner.value, destination) with
      | Some value, Some destination ->
          in_statement st (fun () ->
              (* An earlier [return] may have written part of the result, so
                 the result slot is dropped before it is written again. *)
              if Some destination = result_place st then clear_result st;
              into st value destination)
      | Some value, None -> in_statement st (fun () -> ignore (value_place st value))
      | None, _ -> ())

and statement st (node : Core.statement) =
  in_statement st (fun () ->
      match node.kind with
      | Evaluate { kind = Use source; _ } -> ignore (place st source)
      | Evaluate value -> ignore (value_place st value)
      | Proof _ -> ()
      | Let { pattern = { kind = Bind { local; name; _ }; type_; _ }; value; else_ = None } -> (
          let ty = ground st type_ in
          match value with
          | Place source when not (trivial st ty) ->
              (* A [let] of a place aliases it. A [var] never has a place
                 here: it takes the value. *)
              bind_local st local (Statements.snapshot st (place st source))
          | Place source ->
              let variable = binding st ~name ty in
              take st (place st source) ty ~destination:variable;
              bind_local st local variable
          | Value value ->
              let variable = binding st ~name ty in
              into st value variable;
              bind_local st local variable)
      | Let { pattern; value; else_ } ->
          let scrutinee = operand_place st value in
          let failed = block st.b in
          Option.iter
            (fun else_ ->
              aside st.b failed (fun () ->
                  block_into st else_ None;
                  finish st.b Unreachable))
            else_;
          match_patterns st [ (pattern, scrutinee) ] ~failed
      | Assign { target; value } ->
          (* The new value is evaluated into a temporary before it replaces
             the old one, because evaluating it can read the target. *)
          let ty = ground st value.type_ in
          let target = place st target in
          let new_value = temporary st ty in
          into st value new_value;
          replace st target ty ~by:new_value
      | Assert { value; _ } ->
          let condition = operand st value in
          let failed = block st.b and after = block st.b in
          finish st.b
            (Switch { value = condition; cases = [ (Z.one, after) ]; default = Some failed });
          start st.b failed;
          let message = "assert " ^ source st (spans st).(value.origin) in
          finish st.b
            (Fail
               {
                 failure = Assertion;
                 message = Constant (Bytes message);
                 length = usize (String.length message);
                 site = site_of st node.origin;
               });
          start st.b after
      | Compound_assign { target; value } ->
          (* The target place is evaluated once. The operator reads its
             current value, and the result replaces it. *)
          let ty = ground st value.type_ in
          let target = place st target in
          let result = temporary st ty in
          let enclosing = st.compound_target in
          st.compound_target <- Some target;
          into st value result;
          st.compound_target <- enclosing;
          replace st target ty ~by:result
      | While { condition; body; _ } ->
          (* The condition's temporaries are dropped before the body and
             before the exit. The names it binds live until the body ends. *)
          let test = block st.b and inside = block st.b and failed = block st.b in
          let after = block st.b in
          let depth = List.length st.scopes in
          finish st.b (Goto test);
          start st.b test;
          let names = open_scope st Bindings in
          let tested = open_scope st Statement in
          branch st condition ~yes:inside ~no:failed;
          pop_scope st tested;
          start st.b failed;
          drop_scope st tested;
          drop_scope st names;
          finish st.b (Goto after);
          start st.b inside;
          drop_scope st tested;
          Statements.looping st ~continue_:test ~break_:after ~depth (fun () ->
              block_into st body None);
          close_scope st names;
          finish st.b (Goto test);
          start st.b after
      | For { pattern; iteration = Integer_range { start = low; stop = high; inclusive }; body; _ }
        ->
          let element = ground st low.type_ in
          let index = binding st ~name:"index" element in
          let stop = binding st element in
          emit st.b (Assign (index, Use (operand st low)));
          emit st.b (Assign (stop, Use (operand st high)));
          let test = block st.b
          and inside = block st.b
          and step = block st.b
          and after = block st.b in
          let depth = List.length st.scopes in
          finish st.b (Goto test);
          start st.b test;
          let going = local st.b (Raw Bool) in
          emit st.b
            (Assign
               (at going, Binary ((if inclusive then Less_equal else Less), Copy index, Copy stop)));
          finish st.b
            (Switch { value = Copy (at going); cases = [ (Z.one, inside) ]; default = Some after });
          start st.b inside;
          in_scope st (fun () ->
              let bound = binding st element in
              emit st.b (Assign (bound, Use (Copy index)));
              match_patterns st [ (pattern, bound) ] ~failed:(block st.b);
              Statements.looping st ~continue_:step ~break_:after ~depth (fun () ->
                  block_into st body None));
          finish st.b (Goto step);
          start st.b step;
          (* An inclusive range stops after its last value without adding
             one to it, which could overflow. *)
          if inclusive then begin
            let last = local st.b (Raw Bool) in
            emit st.b (Assign (at last, Binary (Equal, Copy index, Copy stop)));
            let next = block st.b in
            finish st.b
              (Switch { value = Copy (at last); cases = [ (Z.one, after) ]; default = Some next });
            start st.b next
          end;
          emit st.b
            (Assign (index, Binary (Add, Copy index, constant_int (integer_of st element) Z.one)));
          finish st.b (Goto test);
          start st.b after
      | For { pattern; iteration = Yielding_call { kind = Call call; _ }; body; _ } -> (
          (* The yielding method is inlined here, with the loop body at each
             of its [yield]s. *)
          match resolve_callee st call.callee with
          | None -> unhandled "a loop over a call through an any value"
          | Some (path, _) when List.exists (Path.equal path) st.frame.inlined ->
              unhandled "a loop over a recursive yielding method"
          | Some (path, type_arguments) ->
              let signature = signature_of st.context path in
              (match signature.output with
              | Yields _ -> ()
              | Returns _ | Lends _ -> bug "a loop over %s, which does not yield" (Path.show path));
              let substitution = bind signature.generics type_arguments in
              let evaluated, _ = evaluate_arguments st signature substitution call.arguments in
              let arguments =
                List.filter_map Fun.id
                  (List.mapi
                     (fun index ((mode, ty, place), (argument : Core.argument)) ->
                       match argument with
                       | Default -> None
                       | Passed _ -> Some (index, mode, ty, place))
                     (List.combine evaluated call.arguments))
              in
              let caller = st.frame in
              let depth = List.length st.scopes in
              let after = block st.b in
              Calls.inline st path type_arguments ~arguments ~call_site:(site_of st node.origin)
                ~on_yield:(fun yielded ~resume ~stop ->
                  let inner = st.frame in
                  st.frame <- caller;
                  let around = List.length st.scopes in
                  in_scope st (fun () ->
                      match_patterns st [ (pattern, yielded) ] ~failed:(block st.b);
                      st.loops <-
                        {
                          continue_ = resume;
                          continue_depth = around;
                          break_ = after;
                          break_depth = depth;
                        }
                        :: st.loops;
                      block_into st body None;
                      st.loops <- List.tl st.loops);
                  finish st.b (Goto resume);
                  ignore stop;
                  st.frame <- inner);
              finish st.b (Goto after);
              start st.b after)
      | For { iteration = Yielding_call _; _ } -> bug "a loop over what is not a call"
      | For { iteration = Cursor _; _ } -> unhandled "a loop over a cursor"
      | kind -> unhandled (statement_kind kind))

(* Falls through where the value at a place matches a pattern, and goes to
   [failed] where it does not. Binds nothing and moves nothing. *)
and test_pattern st (pattern : Core.pattern) (place : Lir.place) ~failed =
  let require (condition : Lir.rvalue) =
    let holds = local st.b (Raw Bool) and matched = block st.b in
    emit st.b (Assign (at holds, condition));
    finish st.b
      (Switch { value = Copy (at holds); cases = [ (Z.one, matched) ]; default = Some failed });
    start st.b matched
  in
  match pattern.kind with
  | Wildcard | Bind _ -> ()
  | Literal value -> require (Binary (Equal, Copy place, operand st value))
  | Range { start = low; stop = high; inclusive } ->
      require (Binary (Greater_equal, Copy place, operand st low));
      require (Binary ((if inclusive then Less_equal else Less), Copy place, operand st high))
  | Equal_to { value; equal } -> (
      let ty = ground st pattern.type_ in
      let other = value_place st value in
      let result = temporary st st.context.bool in
      match resolve_callee st equal with
      | Some (path, type_arguments) ->
          let signature = signature_of st.context path in
          call_instance st
            (Code { path; type_arguments })
            ~signature
            ~substitution:(bind signature.generics type_arguments)
            ~arguments:[ (Read, ty, place); (Read, ty, other) ]
            ~mask:0 ~destination:result;
          require (Use (Copy result))
      | None -> bug "a pattern compares with what is not a method")
  | Alternatives alternatives ->
      let matched = block st.b in
      let rec test = function
        | [] -> finish st.b (Goto failed)
        | [ last ] ->
            test_pattern st last place ~failed;
            finish st.b (Goto matched)
        | alternative :: rest ->
            let next = block st.b in
            test_pattern st alternative place ~failed:next;
            finish st.b (Goto matched);
            start st.b next;
            test rest
      in
      test alternatives;
      start st.b matched
  | Variant { variant; fields } ->
      require (Is_variant (place, variant));
      List.iter
        (fun (field, inner) ->
          test_pattern st inner (place / Variant_field { variant; field }) ~failed)
        fields
  | Record fields ->
      List.iter (fun (field, inner) -> test_pattern st inner (place / Field field) ~failed) fields

(* Tests values against patterns, none of which has an alternative that
   binds a name, and then the guard. Goes to [failed] where a pattern or the
   guard does not match. Otherwise falls through and returns the names the
   patterns bind. For the guard, each name aliases its part and nothing is
   moved, so a guard that fails leaves the values intact. *)
and test_row st (row : (Core.pattern * Lir.place) list) ~guard ~failed : bound_name list =
  List.iter (fun (pattern, place) -> test_pattern st pattern place ~failed) row;
  let names = List.concat_map (fun (pattern, place) -> bound_names st pattern place) row in
  Option.iter
    (fun guard ->
      List.iter
        (fun bound ->
          bind_name st { bound with mode = (if bound.mode = Own then Read else bound.mode) })
        names;
      let passed = block st.b in
      branch st guard ~yes:passed ~no:failed;
      start st.b passed)
    guard;
  names

(* Tests values against patterns, and then the guard. Where they match,
   falls through with the patterns' names bound in the current scope.
   Otherwise goes to [failed], where the caller drops the current scope. *)
and match_patterns st ?guard (patterns : (Core.pattern * Lir.place) list) ~failed =
  let rows =
    product
      (List.map
         (fun (pattern, place) ->
           List.map (fun pattern -> (pattern, place)) (expand_alternatives pattern))
         patterns)
  in
  match rows with
  | [ row ] -> List.iter (bind_name st) (test_row st row ~guard ~failed)
  | [] -> finish st.b (Goto failed)
  | first :: _ ->
      (* Each row binds the same names from different parts, and the code
         that follows is emitted once, so each name is kept in a slot that
         every row fills. *)
      let slots =
        List.map (fun (pattern, place) -> bound_names st pattern place) first
        |> List.concat
        |> List.map (fun (bound : bound_name) ->
            ( bound.local,
              if has_own_local st bound then Value_slot (binding st ~name:bound.name bound.ty)
              else
                Pointer_slot
                  (local st.b ~name:bound.name
                     (Pointer { target = Value bound.ty; writable = bound.mode = Mut })) ))
      in
      let fill (bound : bound_name) =
        match List.assoc_opt bound.local slots with
        | Some (Value_slot variable) ->
            emit st.b (Assign (variable, Use (owned st bound.part bound.ty)))
        | Some (Pointer_slot pointer) ->
            emit st.b
              (Assign (at pointer, Use (Address { place = bound.part; writable = bound.mode = Mut })))
        | None -> bug "an alternative binds `%s`, which the first alternative does not" bound.name
      in
      let matched = block st.b in
      let rec test = function
        | [] -> ()
        | row :: rest ->
            let next = if rest = [] then failed else block st.b in
            List.iter fill (test_row st row ~guard ~failed:next);
            finish st.b (Goto matched);
            if rest <> [] then start st.b next;
            test rest
      in
      test rows;
      start st.b matched;
      List.iter
        (fun (local, slot) ->
          bind_local st local
            (match slot with
            | Value_slot variable -> variable
            | Pointer_slot pointer -> at pointer / Deref))
        slots

(* Tests the arms in order. Each arm has its own scope for its names and
   the guard's temporaries, which is dropped where the arm does not match. *)
and match_ st ~(scrutinees : Core.operand list) ~(arms : Core.arm list) destination =
  let places = List.map (operand_place st) scrutinees in
  let after = block st.b in
  List.iter
    (fun (arm : Core.arm) ->
      let scope = open_scope st Bindings in
      let unmatched = block st.b in
      match_patterns st ?guard:arm.guard (List.combine arm.patterns places) ~failed:unmatched;
      block_into st arm.body (Some destination);
      close_scope st scope;
      finish st.b (Goto after);
      start st.b unmatched;
      drop_scope st scope)
    arms;
  finish st.b Unreachable;
  start st.b after

(* Lowers the body of the current function into its result slot. Returns an
   error that describes the node kind where the body has one that is not
   handled yet; the caller then discards what was emitted. *)
let body st (form : Core.t) : (unit, string) result =
  match form.definition with
  | Function { body = Some inner; _ } | Test inner -> (
      match block_into st inner (result_place st) with
      | () -> Ok ()
      | exception Unhandled_node what -> Error what)
  | _ -> Error "a definition that has no body"
