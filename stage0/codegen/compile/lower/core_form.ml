(* Lowers a function body from its core form.

   The core form records what the type checker resolved: the callee of each
   call, whether each operand is a place or a value, and every type. So this
   lowering does no name resolution and no type inference. *)

open Definitions
open Lowering
open Targets
open Lir_builder

(* The parameters and the body of a function or a test, from its core
   form. *)
let body_of context path : Core.parameter list * Core.block =
  match demand context Infer.core_of_path path with
  | Some ({ definition = Function { parameters; body = Some body; _ }; _ }, _) -> (parameters, body)
  | Some ({ definition = Test body; _ }, _) -> ([], body)
  | _ -> bug "%s has no body in its core form" (Path.show path)

let spans st =
  match demand st.context Names.spans st.frame.code.definition_key with
  | Some spans -> spans
  | None -> bug "no spans for %s" (Path.show st.frame.code.anchor)

(* The source position of a node, for a failure message. *)
let site_of st (origin : Core.origin) = site st (spans st).(origin)

(* Where a check that fails in the code being lowered is reported: at the
   code's own position, or, for the standard library's code that is
   inlined into a program's, at the program's call. An index past the end
   of a list fails in the library's method, and the index is the
   program's. *)
let failure_site st (origin : Core.origin) =
  match st.frame.reported with Some site -> site | None -> site_of st origin

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
  | Self -> st.frame.self_place <- Some place

let operand_type : Core.operand -> T.ty = function
  | Place place -> Core_walk.place_type place
  | Value value -> value.type_

let binary : Core.comparison -> Lir.binary = function
  | Equal -> Equal
  | Not_equal -> Not_equal
  | Less -> Less
  | Less_equal -> Less_equal
  | Greater -> Greater
  | Greater_equal -> Greater_equal

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
  | Local { local; _ } -> local_place st local
  | Constant { path; _ } -> static_constant st path
  | Field { base; field; _ } -> place st base / Field field
  | Temporary value -> value_place st value
  | Lent { kind = Call call; origin; _ } -> lend st call ~call_site:(failure_site st origin)
  | Lent _ -> bug "a lent place that is not a call"

and operand_place st (operand : Core.operand) : Lir.place =
  match operand with Place source -> place st source | Value value -> value_place st value

(* Evaluates an expression into a new temporary, which lives until the end
   of the statement. *)
and value_place st (value : Core.expression) : Lir.place =
  let ty =
    match value.kind with
    (* These diverge, so the temporary is never read. *)
    | Return _ | Break | Continue | Task_exit _ -> Monomorphic.builtin Unit
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
  | Construct { variant; fields } ->
      let fields =
        List.map
          (fun (name, (field : Core.operand option)) ->
            match field with
            | Some (Value field) -> (name, owned st (value_place st field) (ground st field.type_))
            | Some (Place _) -> bug "a field that is a lent place, in a value that is not yielded"
            | None ->
                (* The default is written in the type's definition, so it is
                   lowered in that definition's frame. *)
                let default = field_default st ty ~variant ~field:name in
                in_type_definition st ty (fun () ->
                    (name, owned st (value_place st default) (ground st default.type_))))
          fields
      in
      assign (Build { ty; variant; fields })
  | Template { call; _ } -> into st call destination
  | Function_value { path; type_arguments } -> (
      (* A named function as a value: an adapter that takes an environment
         and ignores it. *)
      match ty with
      | Function function_type ->
          let function_ =
            Instance.Code
              {
                path;
                type_arguments =
                  List.map
                    (Monomorphic.ground_argument st.context.monomorphic st.frame.code.substitution)
                    type_arguments;
              }
          in
          assign
            (Function_value
               { code = Instance (Adapter { function_; ty = function_type }); environment = None })
      | _ -> bug "a function value of type %s" (Ground.to_string ty))
  | Convert { conversion = Widen; value = inner } ->
      (* A function value has the same representation at a wider type. *)
      into st inner destination
  | Convert { conversion = To_integer | From_integer; _ } ->
      bug "a conversion that exists only in specifications"
  | Copy source ->
      Glue.copy_into st.context.glue st.b ~destination ~source:(operand_place st source) ty
  | Value_parameter parameter -> (
      match
        Monomorphic.ground_argument st.context.monomorphic st.frame.code.substitution
          (Value (Value_parameter parameter))
      with
      | Value number -> assign (Use (constant_of st ty (Integer_value number)))
      | _ -> bug "the value parameter %s is not a number" parameter.name)
  | Collection_literal { elements; construction = Array } ->
      List.iteri (fun index element -> into st element (destination / Index (usize index))) elements
  | Collection_literal { construction = Specification_only; _ } | Map_literal _ ->
      bug "a specification's collection in code that runs"
  | Record_update { base; updates } ->
      into st base destination;
      List.iter
        (fun (path, (value : Core.expression)) ->
          let target =
            List.fold_left (fun place field -> place / Lir.Field field) destination path
          in
          let field_ty = ground st value.type_ in
          let new_value = temporary st field_ty in
          into st value new_value;
          replace st target field_ty ~by:new_value)
        updates
  | Call call -> call_into st value call destination
  | Operator { operation; arguments } ->
      ignore
        (Intrinsics.lower ~checks:st.context.checks st.context.env st.b st.context.types operation
           ~type_arguments:(List.map (fun (a : Core.expression) -> ground st a.type_) arguments)
           (List.map (fun argument -> Intrinsics.Value (operand st argument)) arguments)
           ~destination:(Some destination) ~site:(failure_site st value.origin))
  | Compare { comparison; left; right } ->
      assign (Binary (binary comparison, operand st left, operand st right))
  | Not inner -> assign (Unary (Not, operand st inner))
  | And _ | Or _ | Implies _ | Matches _ ->
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
  | Break -> break_loop st
  | Continue -> continue_loop st
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
  | Provide { implementations; body } ->
      (* The body runs with the evidence of each implementation added. *)
      let enclosing = st.evidence in
      let provided =
        List.map
          (fun (implementation : Core.implementation) ->
            let place = operand_place st implementation.value in
            let pointer =
              if is_zero_size st (ground st implementation.type_) then Lir.Constant Null
              else Address { place; writable = true }
            in
            ( implementation.mode,
              provided_evidence st ~implementation:pointer
                (List.map
                   (fun (provided : Core.provided) ->
                     (provided.capability, provided.impl, provided.arguments))
                   implementation.provides) ))
          implementations
      in
      (* Several tasks may call a [mut] implementation at the same time
         when the body can use [Tasks], which would be a data race on the
         implementation. Its evidence is then replaced by evidence whose
         table locks a mutex around each call. The locks go through the
         [Tasks] that this [provide] lists, or else the enclosing one, so
         that a scheduler sees them. An implementation of [Tasks] is never
         locked: it guards its own state. *)
      let is_tasks (capability, _) = Path.equal capability Core_walk.tasks_capability in
      let tasks =
        if Core_walk.can_use_tasks body then
          Option.map snd (List.find_opt is_tasks (List.concat_map snd provided @ enclosing))
        else None
      in
      let added =
        List.concat_map
          (fun ((mode : T.mode), evidence) ->
            match tasks with
            | Some tasks when mode = Mut && not (List.exists is_tasks evidence) ->
                locked_evidence st ~tasks evidence
            | _ -> evidence)
          provided
      in
      st.evidence <- added @ enclosing;
      block_into st body (Some destination);
      st.evidence <- enclosing
  | To_any { value = inner; trait; evidence } ->
      let inner_ty = ground st inner.type_ in
      let impl, type_arguments = resolve_impl st ~trait ~self_type:inner.type_ ~evidence in
      (* The value is evaluated before its block is allocated, so that
         leaving early during the evaluation leaves no block behind. *)
      let value = value_place st inner in
      any_into st ~any_ty:ty ~inner_ty ~impl ~type_arguments ~value destination
  | Echo inner ->
      into st inner destination;
      echo st destination ty ~site:(site_of st value.origin)
  | Cursor_next cursor -> (
      match ground st (Core_walk.place_type cursor) with
      | Cursor yielding -> call_next st yielding (place st cursor) destination
      | cursor_ty -> bug "next on %s, which is not a cursor" (Ground.to_string cursor_ty))
  | Lambda { parameters; captures; body; _ } ->
      if st.pulling then
        unsupported ~at:(site_of st value.origin) "a lambda in a yielding method that is pulled";
      let function_type =
        match ty with Function f -> f | _ -> bug "a lambda of %s" (Ground.to_string ty)
      in
      nested_function st ~function_type
        ~output:(match value.type_ with T.Function f -> Some f.output | _ -> None)
        ~captures:
          (List.map
             (fun (capture : Core.capture) ->
               (capture.local, local_place st capture.local, ground st capture.type_))
             captures)
        ~bind_capture:bind_local
        ~body:(fun inner parameter_places ->
          List.iter2
            (fun pattern (place, _, _) ->
              match_patterns inner [ (pattern, place) ] ~failed:(block inner.b))
            parameters parameter_places;
          block_into inner body (result_place inner))
        destination
  | Slice { call; _ } -> into st call destination
  | Quantified { quantifier; binder; body } ->
      (* A loop that stops at the first value that decides the answer: one
         the body is false of, for [forall], or true of, for [exists]. *)
      let deciding = quantifier = Exists in
      let pattern, iteration =
        match binder with
        | Over_range { pattern; start; stop; inclusive } ->
            (pattern, Core.Integer_range { start; stop; inclusive })
        | Over_each { pattern; call } -> (pattern, Yielding_call call)
        | Over_collection _ | Over_type _ ->
            bug "a quantifier that only a specification can have, in code that runs"
      in
      assign (Use (Constant (Bool (not deciding))));
      for_each st ~origin:value.origin ~schedule:Sequential ~iteration ~each:(fun bound ->
          match_patterns st [ (pattern, bound) ] ~failed:(block st.b);
          let holds = temporary st st.context.bool in
          in_statement st (fun () -> into st body holds);
          let decided = block st.b and goes_on = block st.b in
          finish st.b
            (Switch
               {
                 value = Copy holds;
                 cases = [ ((if deciding then Z.one else Z.zero), decided) ];
                 default = Some goes_on;
               });
          start st.b decided;
          assign (Use (Constant (Bool deciding)));
          break_loop st;
          start st.b goes_on)
  | Result | Old _ | Yielded | Finished | Identical _ | Specification_function _ | Method_time _ ->
      bug "a specification-only expression in code that runs"
  | Task_exit { tasks; exit } ->
      (* The task evaluates the return value into a temporary of its own
         before it cancels the group. Several tasks may do so at the same
         time, and only the first to cancel moves its value out. *)
      let value =
        match (exit.kind, st.frame.exit, returned_type st) with
        | Return (Some returned), None, Some ty ->
            let value = temporary st ty in
            into st returned value;
            Some value
        | Return (Some returned), _, _ ->
            ignore (value_place st returned);
            None
        | _ -> None
      in
      early_exit st ~tasks ~exit ~value

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
  if !defaulted > 62 then unsupported "a function with more than 62 parameters that have defaults";
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
  | Trait_method { evidence = Dynamic; _ } -> None
  | Trait_method { trait; name; receiver; self_type; type_arguments; evidence } -> (
      match trait_method_key st ~trait ~name ~receiver ~self_type ~type_arguments ~evidence with
      | Code { path; type_arguments } -> Some (path, type_arguments)
      | _ -> bug "a trait method's key")
  | Capability_method _ | Intrinsic _ | Indirect _ -> None

and call_into st (value : Core.expression) (call : Core.call) destination =
  if call.lends <> None then bug "a lending call that is not a lent place";
  match (resolve_callee st call.callee, call.callee) with
  | Some (path, type_arguments), _ -> (
      let signature = signature_of st.context path in
      let substitution = bind signature.generics type_arguments in
      let arguments, mask = evaluate_arguments st signature substitution call.arguments in
      match signature.output with
      | Returns _ ->
          call_instance st
            (Code { path; type_arguments })
            ~signature ~substitution ~arguments ~mask ~destination ()
      | Yields _ ->
          (* A yielding method called outside a [for] loop makes a cursor,
             which holds its arguments. *)
          cursor_into st ~path ~type_arguments ~signature ~arguments ~mask destination
      | Lends _ -> bug "a lending call that is not a lent place")
  | None, Intrinsic { operation; type_arguments } -> (
      match
        intrinsic st operation ~type_arguments call.arguments ~destination:(Some destination)
          ~site:(site_of st value.origin)
      with
      | Some _ -> bug "a lending intrinsic that is not a lent place"
      | None -> ())
  | None, Capability_method { capability; name } ->
      let slot, signature = capability_method st.context capability name in
      let arguments, _ =
        evaluate_arguments st { signature with receiver = None } [] call.arguments
      in
      capability_defaults st ~capability ~name call.arguments arguments;
      if Path.equal capability panic_path then
        (* [Panic.crash] has no evidence: it ends the process at once. *)
        match arguments with
        | [ (_, _, message) ] ->
            ignore
              (Intrinsics.lower ~checks:st.context.checks st.context.env st.b st.context.types Crash
                 ~type_arguments:[] [ Intrinsics.Place message ] ~destination:None
                 ~site:(site_of st value.origin))
        | _ -> bug "Panic.crash takes one message"
      else begin
        let lir_signature, result = entry_signature st.context signature in
        let target =
          Lir.Evidence_call
            { evidence = evidence_of st capability; capability; slot; signature = lir_signature }
        in
        emit st.b
          (Call
             {
               target;
               arguments =
                 List.filter_map (fun (mode, ty, place) -> pass st mode ty place) arguments;
               result = Convention.destination result destination;
             });
        if not lir_signature.returns then unreachable_block st
      end
  | None, Trait_method { trait; name; self_type; _ } -> (
      (* Through an [any] value, which is the receiver. *)
      let any_type =
        match T.substitute st.frame.code.substitution self_type with
        | T.Any reference -> reference
        | receiver -> bug "a call through any on %s" (T.show receiver)
      in
      match List.map (argument_place st) call.arguments with
      | (_, _, any) :: arguments ->
          call_through_any st ~any_type ~trait:trait.trait ~name ~any ~arguments destination
      | [] -> bug "a call through any with no receiver")
  | None, Indirect function_value ->
      let function_type =
        match ground st (operand_type function_value) with
        | Function f -> f
        | callee_ty -> bug "a call of %s" (Ground.to_string callee_ty)
      in
      let value = operand_place st function_value in
      call_indirect st ~function_type ~value
        (List.map
           (fun argument ->
             let _, _, place = argument_place st argument in
             place)
           call.arguments)
        destination
  | None, Function _ -> bug "a function that does not resolve"

(* Evaluates the default of each argument that a call of a capability method
   omits, into the temporary [evaluate_arguments] gave it. The caller
   evaluates these defaults: an entry of a capability's table takes every
   argument, and there is no one implementation to evaluate them. A default
   is written in the capability's definition, so it is lowered in that
   definition's frame. *)
and capability_defaults st ~capability ~name (arguments : Core.argument list) evaluated =
  if List.mem Core.Default arguments then begin
    let receiver =
      match demand st.context Environment.trait_interface capability with
      | Some interface -> (
          match
            List.find_opt (fun (m : T.trait_method) -> m.method_name = name) interface.methods
          with
          | Some declared -> declared.method_receiver
          | None -> bug "%s has no method %s" (Path.show capability) name)
      | None -> bug "no interface for %s" (Path.show capability)
    in
    let path : Path.t = Method { owner = capability; name; receiver } in
    let parameters =
      match demand st.context Infer.core_of_path path with
      | Some ({ definition = Function { parameters; _ }; _ }, _) -> parameters
      | _ -> bug "%s has no core form" (Path.show path)
    in
    let key = key_of st.context capability in
    let caller = st.frame in
    st.frame <-
      {
        caller with
        code =
          {
            caller.code with
            definition_key = key;
            anchor = capability;
            enclosing_impl = None;
            text = text_of st.context key;
            substitution = [];
          };
        bindings = Hashtbl.create 1;
        synthetic = Hashtbl.create 1;
        self_place = None;
      };
    List.iter2
      (fun (parameter : Core.parameter) ((argument : Core.argument), (_, _, place)) ->
        match (argument, parameter.default) with
        | Default, Some default -> into st default place
        | Default, None -> bug "%s is omitted and has no default" parameter.name
        | Passed _, _ -> ())
      parameters
      (List.combine arguments evaluated);
    st.frame <- caller
  end

(* An argument's mode, type, and place, for a call whose callee has no
   signature to read the parameter's type from. *)
and argument_place st (argument : Core.argument) =
  match argument with
  | Passed { mode; value; _ } -> (mode, ground st (operand_type value), operand_place st value)
  | Default -> bug "an omitted argument in a call that has no defaults"

(* Lowers a loop over [iteration]. [each] lowers the loop body for the
   place of one value. The loop is the innermost loop for the body: a
   [break] exits it and a [continue] starts the next iteration. *)
and for_each st ~origin ~(schedule : schedule) ~(iteration : Core.iteration)
    ~(each : Lir.place -> unit) =
  (* [st.next_range] is set when a [parallel for] or a [concurrent for] is
     inlining a method that yields by position. This range loop is then
     the method's loop, and it takes the schedule of the loop in the
     source. *)
  let schedule =
    match (st.next_range, schedule) with
    | Sequential, Chunked when not (may_fork st) -> Sequential
    | Sequential, own -> own
    | inherited, _ -> inherited
  in
  st.next_range <- Sequential;
  (* How an iteration receives a value that the loop owns, such as one
     that a cursor's [next] returned. *)
  let owned_each =
    match schedule with
    | Spawned loop -> fun value -> spawn_with_item st loop value ~owned:true ~each
    | Sequential | Chunked -> each
  in
  (* What a range of a type counts in. A range of [Character] goes from
     U+D7FF to U+E000, since the surrogates between them are no
     characters. *)
  let counting element =
    let scalar = scalar_of st element in
    let constant value : Lir.operand =
      match scalar with
      | Integer integer -> constant_int integer (Z.of_int value)
      | Character -> Constant (Character value)
      | _ -> bug "a range of %s" (Ground.to_string element)
    in
    (scalar, constant, scalar = Character)
  in
  let both first second =
    let answer = local st.b (Raw Bool) in
    emit st.b (Assign (at answer, Binary (Bit_and, first, second)));
    Lir.Copy (at answer)
  in
  let compare op left right =
    let answer = local st.b (Raw Bool) in
    emit st.b (Assign (at answer, Binary (op, left, right)));
    Lir.Copy (at answer)
  in
  match (iteration, schedule) with
  | Integer_range { start = low; stop = high; inclusive }, Chunked ->
      (* The loop is a region that covers a part of the range's indexes,
         counted from 0 as [UInt64], so that a range of any integer type
         has as many indexes as fit. As it is written here it covers them
         all; outlining has it run for parts of them at the same time. *)
      let element = ground st low.type_ in
      let scalar, constant, characters = counting element in
      let wide = Lir.Raw (Integer UInt64) in
      let one = constant_int UInt64 Z.one in
      let first_value = binding st ~name:"start" element in
      let last_value = binding st element in
      emit st.b (Assign (first_value, Use (operand st low)));
      emit st.b (Assign (last_value, Use (operand st high)));
      let going = local st.b (Raw Bool) in
      emit st.b
        (Assign
           ( at going,
             Binary ((if inclusive then Less_equal else Less), Copy first_value, Copy last_value) ));
      let inside = block st.b and after = block st.b in
      let depth = List.length st.scopes in
      Lir_builder.branch st.b (Copy (at going)) ~yes:inside ~no:after;
      start st.b inside;
      let first = local st.b ~name:"first" wide and last = local st.b ~name:"last" wide in
      let low_wide = local st.b wide and high_wide = local st.b wide in
      emit st.b (Assign (at first, Use (constant_int UInt64 Z.zero)));
      emit st.b (Assign (at low_wide, Convert (Copy first_value, Integer UInt64)));
      emit st.b (Assign (at high_wide, Convert (Copy last_value, Integer UInt64)));
      emit st.b (Assign (at last, Binary (Subtract, Copy (at high_wide), Copy (at low_wide))));
      if not inclusive then emit st.b (Assign (at last, Binary (Subtract, Copy (at last), one)));
      if characters then
        when_ st.b
          (both
             (compare Less (Copy first_value) (constant 0xD800))
             (compare Greater (Copy last_value) (constant 0xDFFF)))
          (fun () ->
            emit st.b
              (Assign
                 (at last, Binary (Subtract, Copy (at last), constant_int UInt64 (Z.of_int 0x800)))));
      let fork = fresh_fork st in
      emit st.b (Region { fork; region = Chunk { first; last } });
      let index = local st.b ~name:"index" wide in
      emit st.b (Assign (at index, Use (Copy (at first))));
      let again = block st.b and step = block st.b and done_ = block st.b in
      finish st.b (Goto again);
      start st.b again;
      in_scope st (fun () ->
          let offset = binding st element in
          let bound = binding st element in
          emit st.b (Assign (offset, Convert (Copy (at index), scalar)));
          emit st.b (Assign (bound, Binary (Add, Copy first_value, Copy offset)));
          if characters then
            when_ st.b
              (both
                 (compare Less (Copy first_value) (constant 0xD800))
                 (compare Greater_equal (Copy bound) (constant 0xD800)))
              (fun () -> emit st.b (Assign (bound, Binary (Add, Copy bound, constant 0x800))));
          looping st ~continue_:step ~break_:done_ ~depth (fun () -> each bound));
      finish st.b (Goto step);
      start st.b step;
      let ended = local st.b (Raw Bool) in
      emit st.b (Assign (at ended, Binary (Equal, Copy (at index), Copy (at last))));
      let next = block st.b in
      Lir_builder.branch st.b (Copy (at ended)) ~yes:done_ ~no:next;
      start st.b next;
      emit st.b (Assign (at index, Binary (Add, Copy (at index), one)));
      finish st.b (Goto again);
      start st.b done_;
      emit st.b (Regions_end { fork });
      finish st.b (Goto after);
      start st.b after
  | Integer_range { start = low; stop = high; inclusive }, (Sequential | Spawned _) ->
      let element = ground st low.type_ in
      let scalar, constant, characters = counting element in
      let index = binding st ~name:"index" element in
      let stop = binding st element in
      emit st.b (Assign (index, Use (operand st low)));
      emit st.b (Assign (stop, Use (operand st high)));
      let test = block st.b and inside = block st.b and step = block st.b and after = block st.b in
      let depth = List.length st.scopes in
      finish st.b (Goto test);
      start st.b test;
      let going = local st.b (Raw Bool) in
      emit st.b
        (Assign (at going, Binary ((if inclusive then Less_equal else Less), Copy index, Copy stop)));
      Lir_builder.branch st.b (Copy (at going)) ~yes:inside ~no:after;
      start st.b inside;
      looping st ~continue_:step ~break_:after ~depth (fun () ->
          let run value =
            in_scope st (fun () ->
                let bound = binding st element in
                emit st.b (Assign (bound, value));
                each bound)
          in
          match schedule with
          | Spawned loop ->
              (* The task's argument is the index, converted to [UInt64]
                 and back. *)
              let item = at loop.item in
              emit st.b (Assign (item, Convert (Copy index, Integer UInt64)));
              spawn_iteration st loop ~not_spawned:ignore (fun () ->
                  run (Convert (Copy item, scalar)))
          | Sequential | Chunked -> run (Use (Copy index)));
      finish st.b (Goto step);
      start st.b step;
      (* An inclusive range stops after its last value without adding
         one to it, which could overflow. *)
      if inclusive then begin
        let last = local st.b (Raw Bool) in
        emit st.b (Assign (at last, Binary (Equal, Copy index, Copy stop)));
        let next = block st.b in
        Lir_builder.branch st.b (Copy (at last)) ~yes:after ~no:next;
        start st.b next
      end;
      emit st.b (Assign (index, Binary (Add, Copy index, constant 1)));
      if characters then
        when_ st.b
          (compare Equal (Copy index) (constant 0xD800))
          (fun () -> emit st.b (Assign (index, Use (constant 0xE000))));
      finish st.b (Goto test);
      start st.b after
  | Yielding_call ({ kind = Call call; _ } as iterated), _ -> (
      (* The yielding method is inlined here, with the loop body at each
         of its [yield]s. *)
      match resolve_callee st call.callee with
      | None -> bug "a loop over a call that resolves to no method"
      | Some (path, type_arguments) when List.exists (Path.equal path) st.frame.inlined ->
          (* The method is already inlined around this loop, so inlining
             it again would never end. The loop pulls a cursor over the
             call instead. *)
          let yielding : Ground.yielding = { method_ = path; type_arguments } in
          in_scope st (fun () ->
              let cursor = boxed_cursor st yielding in
              call_into st iterated call cursor;
              own_in_scope st cursor;
              pull_cursor st yielding cursor ~each:owned_each)
      | Some (path, type_arguments) ->
          let mode =
            match (signature_of st.context path).output with
            | Yields (mode, _) -> mode
            | Returns _ | Lends _ -> bug "a loop over %s, which does not yield" (Path.show path)
          in
          let arguments = arguments_to_inline st path type_arguments call.arguments in
          let caller = st.frame in
          let depth = List.length st.scopes in
          let after = block st.b in
          (* A method that yields by position has one range loop, and that
             loop takes this loop's schedule. Any other method runs
             sequentially in the enclosing code, and a task is spawned at
             each of its [yield]s with the yielded value. The task outlives
             the [yield]. The ownership check has verified that a place
             the task borrows stays valid and unchanged until the group is
             joined, and it rejects a [yield] of a [mut] place. *)
          let each_yielded =
            match schedule with
            | (Chunked | Spawned _) when yields_by_position st path ->
                st.next_range <- schedule;
                fun value ~owned:_ -> each value
            | Sequential | Chunked -> fun value ~owned:_ -> each value
            | Spawned loop ->
                if mode = Mut then
                  bug "a `concurrent for` over %s, which yields `mut` places and not by position"
                    (Path.show path);
                fun value ~owned -> spawn_with_item st loop value ~owned ~each
          in
          inline st path type_arguments ~arguments ~call_site:(site_of st origin)
            ~on_yield:(fun yielded ~owned ~resume ~stop ->
              let inner = st.frame in
              st.frame <- caller;
              let scope_depth = List.length st.scopes in
              in_scope st (fun () ->
                  st.loops <-
                    {
                      continue_ = resume;
                      continue_depth = scope_depth;
                      break_ = after;
                      break_depth = depth;
                    }
                    :: st.loops;
                  each_yielded yielded ~owned;
                  st.loops <- List.tl st.loops);
              finish st.b (Goto resume);
              ignore stop;
              st.frame <- inner);
          finish st.b (Goto after);
          start st.b after)
  | Yielding_call _, _ -> bug "a loop over what is not a call"
  | Cursor { cursor; next = None }, _ -> (
      match ground st (Core_walk.place_type cursor) with
      | Cursor yielding -> pull_cursor st yielding (place st cursor) ~each:owned_each
      | cursor_ty -> bug "a loop over %s, which is not a cursor" (Ground.to_string cursor_ty))
  | Cursor { cursor; next = Some next }, _ ->
      (* A value of a type that implements [Cursor]: its own [next] is
         called until it gives [None]. *)
      let cursor = place st cursor in
      pull_loop st ~option:(result_type st next)
        ~call_next:(fun destination -> call_with_places st next [ cursor ] ~destination)
        ~body:owned_each

and yields_by_position st path =
  let _, (body : Core.block) = body_of st.context path in
  Core_walk.yields_by_position body

(* A loop over the cursor of a yielding method's call: the pulled method's
   [next] is called until it gives [None]. *)
and pull_cursor st (yielding : Ground.yielding) cursor ~(each : Lir.place -> unit) =
  pull_loop st
    ~option:(cursor_result st.context yielding)
    ~call_next:(fun destination -> call_next st yielding cursor destination)
    ~body:each

(* The value a method yields with places lent into it.

   Lent to be read, it holds the bytes of each place and owns nothing, so
   nothing drops it, and the places keep their values.

   Lent to be changed, each place's value is moved into it, and the scope
   around moves each back as it ends, on every way out. So while the caller
   has it, it owns what it holds: a field the caller replaces is dropped
   first, as in any value, and what goes back is whatever the caller left. *)
and lending st (mode : T.mode) (built : Core.expression) : Lir.place =
  let changed = mode = Mut in
  let lent = at (local st.b ~borrowed:(not changed) (Value (ground st built.type_))) in
  (* Once each place has its value back, what is left owns nothing, and
     this drop, which comes after them, says so. *)
  if changed then begin
    let scope = innermost_scope st in
    scope.owned <- Drop_value lent :: scope.owned
  end;
  let lent_operand source ty ~from =
    if changed then begin
      let scope = innermost_scope st in
      scope.owned <- Give_back { lent = from; source; ty } :: scope.owned;
      owned st source ty
    end
    else Lir.Copy source
  in
  construct_lending st built ~borrowed:(not changed) ~lent:lent_operand ~destination:lent
    ~field_path:lent;
  lent

(* For a cursor, whose caller keeps what [next] gives it: the value with a
   copy of each place in place of the place, which it owns. *)
and copied st (built : Core.expression) : Lir.place =
  let copy = temporary st (ground st built.type_) in
  let copy_of source ty ~from:_ =
    let fresh_copy = temporary st ty in
    Glue.copy_into st.context.glue st.b ~destination:fresh_copy ~source ty;
    owned st fresh_copy ty
  in
  construct_lending st built ~borrowed:false ~lent:copy_of ~destination:copy ~field_path:copy;
  copy

(* Builds a construct that has places for fields, at any depth, into
   [destination]. [lent] gives the operand for a place of a type, and is
   told where the field will be within the outermost value, [field_path]. A
   construct inside another is built in a local of its own, which owns
   nothing where [borrowed]. *)
and construct_lending st (built : Core.expression) ~borrowed ~lent ~destination ~field_path =
  match built.kind with
  | Construct { variant; fields } ->
      let ty = ground st built.type_ in
      let part name : Lir.projection =
        match variant with
        | Some variant -> Variant_field { variant; field = name }
        | None -> Field name
      in
      let fields =
        List.map
          (fun (name, (field : Core.operand option)) ->
            match field with
            | Some (Place source) ->
                ( name,
                  lent
                    (snapshot st (place st source))
                    (ground st (Core_walk.place_type source))
                    ~from:(field_path / part name) )
            | Some (Value ({ kind = Construct _; _ } as nested))
              when Core_walk.lent_places (Value nested) <> [] ->
                let ty = ground st nested.type_ in
                let inner = at (local st.b ~borrowed (Value ty)) in
                construct_lending st nested ~borrowed ~lent ~destination:inner
                  ~field_path:(field_path / part name);
                (name, if borrowed then Lir.Copy inner else owned st inner ty)
            | Some (Value value) -> (name, owned st (value_place st value) (ground st value.type_))
            | None ->
                let default = field_default st ty ~variant ~field:name in
                in_type_definition st ty (fun () ->
                    (name, owned st (value_place st default) (ground st default.type_))))
          fields
      in
      emit st.b (Assign (destination, Build { ty; variant; fields }))
  | _ -> bug "a value that lends places and is no construct"

(* The type that the current frame's method yields. *)
and yielded_type_of_frame st =
  match st.frame.code.result with
  | Yields (_, ty) | Lends (_, ty) -> ground st ty
  | Returns _ -> bug "a yield in %s, which does not yield" (Path.show st.frame.code.anchor)

(* The function or method that a callee resolves to, with its type
   arguments, its signature, and the substitution for its generic
   parameters. *)
and resolved st (callee : Core.callee) =
  match resolve_callee st callee with
  | Some (path, type_arguments) ->
      let signature = signature_of st.context path in
      (path, type_arguments, signature, bind signature.generics type_arguments)
  | None -> bug "a callee that is not a function or a method"

and result_type st (callee : Core.callee) =
  let path, _, signature, substitution = resolved st callee in
  match signature.output with
  | Returns ty -> Monomorphic.ground st.context.monomorphic substitution ty
  | Yields _ | Lends _ -> bug "%s does not return a value" (Path.show path)

(* Calls a function or a method with arguments that are already in places,
   one for each parameter in order. *)
and call_with_places st (callee : Core.callee) (places : Lir.place list) ~destination =
  let path, type_arguments, signature, substitution = resolved st callee in
  let arguments =
    List.map2
      (fun (mode, ty) place ->
        (mode, Monomorphic.ground st.context.monomorphic substitution ty, place))
      (interface_parameters signature) places
  in
  call_instance st
    (Code { path; type_arguments })
    ~signature ~substitution ~arguments ~destination ()

(* The default of a field, from the core form of the type's definition. *)
and field_default st (ty : Ground.ty) ~variant ~field : Core.expression =
  let path =
    match ty with Named { path; _ } -> path | _ -> bug "defaults of %s" (Ground.to_string ty)
  in
  match demand st.context Infer.core_of_path path with
  | Some ({ definition = Type { defaults; _ }; _ }, _) -> (
      match
        List.find_opt (fun (of_variant, name, _) -> of_variant = variant && name = field) defaults
      with
      | Some (_, _, default) -> default
      | None -> bug "%s has no default for %s" (Path.show path) field)
  | _ -> bug "%s has no core form" (Path.show path)

(* Lowers a call of an intrinsic. Returns the place it lends, for one that
   lends. *)
and intrinsic st operation ~type_arguments (arguments : Core.argument list) ~destination ~site =
  match ((operation : Intrinsic.operation), arguments) with
  | Shared_update, [ shared; input; change ] ->
      shared_update st ~shared ~input ~change ~destination;
      None
  | _ -> intrinsic_operation st operation ~type_arguments arguments ~destination ~site

(* Lowers [shared_update]: locks the shared value's mutex, calls [change]
   on the value and the input, and unlocks the mutex. *)
and shared_update st ~shared ~input ~change ~destination =
  let _, _, shared = argument_place st shared in
  let _, _, input = argument_place st input in
  let _, change_ty, change = argument_place st change in
  let function_type =
    match change_ty with
    | Function function_type -> function_type
    | ty -> bug "shared_update with a %s, which is not a function" (Ground.to_string ty)
  in
  let value_ty, result_ty =
    match (function_type.parameters, function_type.result) with
    | (_, value_ty) :: _, Returns result_ty -> (value_ty, result_ty)
    | _ -> bug "shared_update with a function that takes no value or returns none"
  in
  let pointer = Lir.Copy (shared / Field "value") in
  emit st.b (Call { target = Intrinsic Shared_lock; arguments = [ pointer ]; result = Discarded });
  (* The pointer is [borrowed] so that drop elaboration does not track the
     value, which the [Shared] owns. *)
  let typed = local st.b ~borrowed:true (Pointer { target = Value value_ty; writable = true }) in
  emit st.b (Assign (at typed, Use pointer));
  let result =
    match destination with Some destination -> destination | None -> temporary st result_ty
  in
  call_indirect st ~function_type ~value:change
    [ { root = Local typed; projections = [ Deref ] }; input ]
    result;
  emit st.b (Call { target = Intrinsic Shared_unlock; arguments = [ pointer ]; result = Discarded })

and intrinsic_operation st operation ~type_arguments (arguments : Core.argument list) ~destination
    ~site =
  let ground_arguments =
    List.map
      (Monomorphic.ground_argument st.context.monomorphic st.frame.code.substitution)
      type_arguments
  in
  let type_arguments =
    List.filter_map (function Ground.Type ty -> Some ty | _ -> None) ground_arguments
  and value_arguments =
    List.filter_map (function Ground.Value value -> Some value | _ -> None) ground_arguments
  in
  let arguments =
    List.map
      (fun (argument : Core.argument) ->
        match argument with
        | Passed { value = Place source; _ } -> Intrinsics.Place (place st source)
        | Passed { mode; value = Value value; _ } ->
            let ty = ground st value.type_ in
            let evaluated = value_place st value in
            (* An intrinsic takes storage and views by place. *)
            if Storage.elements_of ty <> None || Storage.viewed ty <> None then
              Intrinsics.Place evaluated
            else Intrinsics.Value (if mode = T.Own then owned st evaluated ty else Copy evaluated)
        | Default -> bug "an intrinsic called with an omitted argument")
      arguments
  in
  Intrinsics.lower ~checks:st.context.checks ~value_arguments st.context.env st.b st.context.types
    operation ~type_arguments arguments ~destination ~site

(* The place that a lending call lends. A lending method is inlined up to
   its [yield]; a lending intrinsic gives the place directly. *)
and lend st (call : Core.call) ~call_site : Lir.place =
  match call.callee with
  | Intrinsic { operation; type_arguments } -> (
      match
        intrinsic st operation ~type_arguments call.arguments ~destination:None ~site:call_site
      with
      | Some place -> place
      | None -> bug "a lent place from an intrinsic that does not lend")
  | callee -> (
      match resolve_callee st callee with
      | Some (path, type_arguments) ->
          let arguments = arguments_to_inline st path type_arguments call.arguments in
          inline_lending st path type_arguments ~arguments ~call_site
      | None -> bug "a lending call that resolves to no method")

(* Evaluates the arguments of a call that is inlined: each with its
   parameter's index, without the omitted ones, which the inlined method
   fills from its defaults. *)
and arguments_to_inline st path type_arguments (arguments : Core.argument list) =
  let signature = signature_of st.context path in
  let substitution = bind signature.generics type_arguments in
  let evaluated, _ = evaluate_arguments st signature substitution arguments in
  List.filter_map Fun.id
    (List.mapi
       (fun index ((mode, ty, place), (argument : Core.argument)) ->
         match argument with Default -> None | Passed _ -> Some (index, mode, ty, place))
       (List.combine evaluated arguments))

and return_ st (returned : Core.expression option) =
  (match (returned, st.frame.exit, result_place st) with
  | Some returned, None, Some result ->
      clear_result st;
      into st returned result
  | Some returned, _, _ -> ignore (value_place st returned)
  | None, _, _ -> ());
  return_from_frame st

(* Evidence for the capabilities of one [mut] implementation whose calls
   are mutually exclusive. The implementation's capabilities share one
   mutex, a word in this frame. The evidence for each capability has the
   capability's locking table, the mutex's address as its implementation
   pointer, and the implementation's own evidence and the evidence for
   [Tasks] as its outer evidence. *)
and locked_evidence st ~(tasks : Lir.operand) (evidence : (Path.t * Lir.operand) list) =
  let mutex = at (local st.b ~name:"mutex" (Value (Monomorphic.builtin UInt64))) in
  emit st.b (Assign (mutex, Use (constant_int UInt64 Z.zero)));
  List.map
    (fun (capability, implementation) ->
      let slot = local st.b (Evidence 2) in
      emit st.b
        (Call
           {
             target = Intrinsic Evidence_fill;
             arguments =
               [
                 Address { place = at slot; writable = true };
                 Address { place = mutex; writable = true };
                 Constant (Symbol_address (Locked_table capability));
                 implementation;
                 tasks;
               ];
             result = Discarded;
           });
      (capability, Lir.Address { place = at slot; writable = false }))
    evidence

(* Returns from the function, whose result is already written. In an
   inlined method, jumps to the method's end instead. *)
and return_from_frame st =
  (match st.frame.exit with
  | Some (exit, depth) ->
      leave_to st depth;
      finish st.b (Goto exit)
  | None ->
      leave_to st 0;
      finish st.b (return_result st));
  start st.b (block st.b)

and break_loop st =
  match st.loops with
  | loop :: _ ->
      leave_to st loop.break_depth;
      finish st.b (Goto loop.break_);
      start st.b (block st.b)
  | [] -> bug "a break outside a loop"

and continue_loop st =
  match st.loops with
  | loop :: _ ->
      leave_to st loop.continue_depth;
      finish st.b (Goto loop.continue_);
      start st.b (block st.b)
  | [] -> bug "a continue outside a loop"

(* A call of the [Tasks] method [name]. [places] holds one argument for
   each parameter, and the call writes its return value to [result]. *)
and tasks_call st name ?result (places : Lir.place list) : Lir.statement =
  let capability = Core_walk.tasks_capability in
  let slot, signature = capability_method st.context capability name in
  let lir_signature, convention = entry_signature st.context signature in
  Call
    {
      target =
        Evidence_call
          { evidence = evidence_of st capability; capability; slot; signature = lir_signature };
      arguments =
        List.filter_map Fun.id
          (List.map2
             (fun (mode, ty) place ->
               pass st mode (Monomorphic.ground st.context.monomorphic [] ty) place)
             (interface_parameters { signature with receiver = None })
             places);
      result =
        (match result with
        | Some place -> Convention.destination convention place
        | None -> Discarded);
    }

(* Calls a [Tasks] method that returns a [Bool], and gives the result. *)
and tasks_bool st name places : Lir.operand =
  let result = at (local st.b (Value st.context.bool)) in
  emit st.b (tasks_call st name ~result places);
  Copy result

(* Opens a task group, runs [f] with it, and joins it. A scope owns the
   join, so an early exit from [f] joins the group too. The scope's other
   temporaries are dropped after the join, because a task may still read
   them until then. *)
and with_group st ~origin (f : Lir.place -> unit) =
  if st.pulling then
    unsupported ~at:(site_of st origin) "`concurrent` code in a yielding method that is pulled";
  let scope = open_scope st Statement in
  let group = at (local st.b ~name:"group" (Value (Monomorphic.builtin UInt64))) in
  emit st.b (tasks_call st "open" ~result:group []);
  let join = tasks_call st "join" [ group ] in
  let cleanup = Join_group join in
  scope.owned <- [ cleanup ];
  f group;
  emit st.b join;
  scope.owned <- List.filter (fun owned -> owned != cleanup) scope.owned;
  close_scope st scope

(* The type of the function value that [Tasks.spawn] takes. *)
and task_function_type st : Lir.ty =
  let _, signature = capability_method st.context Core_walk.tasks_capability "spawn" in
  match signature.parameters with
  | [ _; work; _ ] -> Value (Monomorphic.ground st.context.monomorphic [] work.type_)
  | _ -> bug "Tasks.spawn does not take a group, a function, and an item"

(* Lowers the body of a task with [f]. The body starts at the region mark
   that the caller has just emitted. Every exit from the task jumps to
   [end_block], which is the current block when this returns. *)
and task_body st ~(id : Core.task) ~group ~early_exits (f : task -> unit) =
  let task =
    { id; group; early_exits; end_block = block st.b; scope_depth = List.length st.scopes }
  in
  st.tasks <- task :: st.tasks;
  f task;
  st.tasks <- List.tl st.tasks;
  finish st.b (Goto task.end_block);
  start st.b task.end_block

(* Lowers an early exit that still has to end [tasks], the enclosing tasks
   it leaves, innermost first. [value] holds the return value of a
   [return] that has one.

   With no task left, this is the plain exit. Otherwise the innermost task
   cancels its group. If it is the first to cancel, it records the exit's
   number and the return value for the code that joins the group. The task
   then ends, whether or not it was first. *)
and early_exit st ~(tasks : Core.task list) ~(exit : Core.expression) ~(value : Lir.place option) =
  match (tasks, st.tasks) with
  | [], _ -> (
      match exit.kind with
      | Return _ ->
          (match (value, result_place st, returned_type st) with
          | Some value, Some result, Some ty ->
              clear_result st;
              emit st.b (Assign (result, Use (owned st value ty)))
          | _ -> ());
          return_from_frame st
      | Break -> break_loop st
      | Continue -> continue_loop st
      | _ -> bug "an early exit that is not a return, a break, or a continue")
  | id :: rest, task :: _ when id = task.id ->
      let exits = task.early_exits in
      exits.exits <- (rest, exit) :: exits.exits;
      let number = List.length exits.exits in
      when_ st.b (tasks_bool st "cancel" [ task.group ]) (fun () ->
          emit st.b (Assign (exits.winner, Use (constant_int UInt32 (Z.of_int number))));
          match (value, returned_type st) with
          | Some value, Some ty ->
              let return_value =
                match exits.return_value with
                | Some return_value -> return_value
                | None ->
                    let return_value = owned_local st ~name:"return_value" exits.scope ty in
                    exits.return_value <- Some return_value;
                    return_value
              in
              (* Only one exit wins, so [return_value] is empty here. Drop
                 elaboration cannot prove that when a loop repeats this
                 code, so the assignment is lowered as a replacement. *)
              replace st return_value ty ~by:value
          | _ -> ());
      leave_to st task.scope_depth;
      finish st.b (Goto task.end_block);
      start st.b (block st.b)
  | _ -> bug "an early exit leaves a task that is not the innermost enclosing task"

(* After a group is joined: if one of its tasks' early exits won, performs
   that exit in the enclosing code. *)
and resume_early_exit st ~of_loop (exits : early_exits) =
  match List.rev exits.exits with
  | [] -> ()
  | recorded ->
      let after = block st.b in
      let targets = List.map (fun _ -> block st.b) recorded in
      finish st.b
        (Switch
           {
             value = Copy exits.winner;
             cases = List.mapi (fun index target -> (Z.of_int (index + 1), target)) targets;
             default = Some after;
           });
      List.iter2
        (fun target ((tasks, exit) : Core.task list * Core.expression) ->
          start st.b target;
          (match (tasks, exit.kind) with
          (* A [break] of the [concurrent for] itself. The loop has already
             ended. *)
          | [], Break when of_loop -> ()
          | _, Return _ -> early_exit st ~tasks ~exit ~value:exits.return_value
          | _ -> early_exit st ~tasks ~exit ~value:None);
          finish st.b (Goto after))
        targets recorded;
      start st.b after

(* Lowers a [concurrent] block. Each branch is a [Task] region, which
   outlining turns into a nested function. The code after the regions
   spawns each function as a task of one group. *)
and concurrent_block st ~origin (branches : Core.statement list) =
  let function_type = task_function_type st in
  let item = local st.b (Value (Monomorphic.builtin UInt64)) in
  emit st.b (Assign (at item, Use (constant_int UInt64 Z.zero)));
  let branches =
    List.mapi
      (fun index branch ->
        (index, branch, new_early_exits st, local st.b ~name:"task" function_type))
      branches
  in
  if branches <> [] then
    with_group st ~origin (fun group ->
        let fork = fresh_fork st in
        List.iter
          (fun (index, branch, early_exits, function_value) ->
            emit st.b (Region { fork; region = Task { function_value; item } });
            task_body st
              ~id:(Branch { block = origin; index })
              ~group ~early_exits
              (fun _ -> statement st branch))
          branches;
        emit st.b (Regions_end { fork });
        (* [spawn] returns false once the group is cancelled, and the
           branch then never runs. *)
        List.iter
          (fun (_, _, _, function_value) ->
            ignore (tasks_bool st "spawn" [ group; at function_value; at item ]))
          branches);
  List.iter (fun (_, _, early_exits, _) -> resume_early_exit st ~of_loop:false early_exits) branches

(* Lowers a [concurrent for] loop. The enclosing code runs the iteration
   and spawns one task for each value. *)
and concurrent_for st ~origin ~(pattern : Core.pattern) ~iteration ~(body : Core.block) =
  let early_exits = new_early_exits st in
  with_group st ~origin (fun group ->
      let loop =
        {
          origin;
          group;
          early_exits;
          item = local st.b ~name:"item" (Value (Monomorphic.builtin UInt64));
          element = ground st pattern.type_;
        }
      in
      for_each st ~origin ~schedule:(Spawned loop) ~iteration ~each:(fun value ->
          match_patterns st [ (pattern, value) ] ~failed:(block st.b);
          block_into st body None));
  resume_early_exit st ~of_loop:true early_exits

(* Spawns one iteration of a [concurrent for] loop as a task. [f] lowers
   the iteration's body, and the task's argument is the current value of
   [loop.item]. If the group is already cancelled, [spawn] returns false:
   [not_spawned] then releases what the item owns, and the enclosing code
   breaks out of the loop that produces the items. *)
and spawn_iteration st (loop : spawn_loop) ~(not_spawned : unit -> unit) (f : unit -> unit) =
  let fork = fresh_fork st in
  let function_value = local st.b ~name:"task" (task_function_type st) in
  emit st.b (Region { fork; region = Task { function_value; item = loop.item } });
  task_body st
    ~id:(Iteration { loop = loop.origin })
    ~group:loop.group ~early_exits:loop.early_exits
    (fun task ->
      (* A [continue] of the loop ends the task. A [break] of the loop
         never jumps: it is an early exit that ends the task. *)
      looping st ~continue_:task.end_block ~break_:task.end_block ~depth:task.scope_depth f);
  emit st.b (Regions_end { fork });
  let spawned = tasks_bool st "spawn" [ loop.group; at function_value; at loop.item ] in
  let next = block st.b and cancelled = block st.b in
  Lir_builder.branch st.b spawned ~yes:next ~no:cancelled;
  start st.b cancelled;
  not_spawned ();
  break_loop st;
  start st.b next

(* Spawns one iteration of a [concurrent for] loop with the value at
   [value]. The value's bytes go into a heap block, the block's address is
   the task's argument, and the task takes the bytes out and frees the
   block. A zero-sized value needs no block.

   If the loop owns the value ([owned]), it is moved, and the task owns
   and drops it. Otherwise the bytes are a bitwise copy of a borrowed
   place, and the task never drops them: the place still owns what they
   point at, and it outlives the task. *)
and spawn_with_item st (loop : spawn_loop) (value : Lir.place) ~owned:is_owned
    ~(each : Lir.place -> unit) =
  let ty = loop.element in
  let item = at loop.item in
  let boxed = not (is_zero_size st ty) in
  let move_or_copy place : Lir.operand = if is_owned then owned st place ty else Copy place in
  (* The block's address, read back from the item, and the value's place
     in the block. The pointer is [borrowed] so that drop elaboration does
     not track the block's contents. *)
  let block_of () : Lir.local * Lir.place =
    let pointer = local st.b (Raw (Pointer Opaque)) in
    emit st.b (Assign (at pointer, Convert (Copy item, Pointer Opaque)));
    let typed = local st.b ~borrowed:true (Pointer { target = Value ty; writable = true }) in
    emit st.b (Assign (at typed, Use (Copy (at pointer))));
    (pointer, { root = Local typed; projections = [ Deref ] })
  in
  (* Takes the value out of the block into a local and frees the block.
     The enclosing scope drops the local only if the value is owned. *)
  let unbox () : Lir.place =
    if boxed then begin
      let unboxed = if is_owned then binding st ty else at (local st.b ~borrowed:true (Value ty)) in
      let pointer, inside = block_of () in
      emit st.b (Assign (unboxed, Use (move_or_copy inside)));
      emit st.b
        (Call { target = Intrinsic Free; arguments = [ Copy (at pointer) ]; result = Discarded });
      unboxed
    end
    else at (local st.b (Value ty))
  in
  if boxed then begin
    let pointer = local st.b (Raw (Pointer Opaque)) in
    emit st.b
      (Call
         {
           target = Intrinsic Allocate;
           arguments = [ Constant (Size_of ty); Constant (Alignment_of ty) ];
           result = Returned (at pointer);
         });
    emit st.b (Assign (item, Convert (Copy (at pointer), Integer UInt64)));
    emit st.b (Assign (snd (block_of ()), Use (move_or_copy value)))
  end
  else emit st.b (Assign (item, Use (constant_int UInt64 Z.zero)));
  spawn_iteration st loop
    ~not_spawned:(fun () -> in_scope st (fun () -> ignore (unbox ())))
    (fun () -> in_scope st (fun () -> each (unbox ())))

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
  | Implies (left, right) ->
      (* A [requires] clause of a tag's [from_template], which a template's
         check evaluates while compiling, may hold [==>]. It holds where
         [left] does not, and [right] is evaluated only where [left] holds,
         since [right] may be defined only there. *)
      let middle = block st.b in
      branch st left ~yes:middle ~no:yes;
      start st.b middle;
      branch st right ~yes ~no
  | Not inner -> branch st inner ~yes:no ~no:yes
  | Matches { value; pattern } ->
      match_patterns st [ (pattern, operand_place st value) ] ~failed:no;
      finish st.b (Goto yes)
  | _ ->
      let value = operand st condition in
      Lir_builder.branch st.b value ~yes ~no

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
      | Concurrent branches -> concurrent_block st ~origin:node.origin branches
      | For { pattern; iteration; body; mode = Concurrent_loop; _ } ->
          concurrent_for st ~origin:node.origin ~pattern ~iteration ~body
      | Parallel statements when may_fork st ->
          (* Each branch is a region, which outlining makes a function of
             its own once drops are elaborated. A branch cannot leave the
             block early, so its region has one way out. *)
          let fork = fresh_fork st in
          List.iter
            (fun branch ->
              emit st.b (Region { fork; region = Branch });
              statement st branch)
            statements;
          emit st.b (Regions_end { fork })
      | Parallel statements -> List.iter (statement st) statements
      | Let { pattern = { kind = Bind { local; name; _ }; type_; _ }; value; else_ = None } -> (
          let ty = ground st type_ in
          match value with
          | Place source when not (trivial st ty) ->
              (* A [let] of a place aliases it. A [var] never has a place
                 here: it takes the value. *)
              bind_local st local (snapshot st (place st source))
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
              in_block st.b failed (fun () ->
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
          Lir_builder.branch st.b condition ~yes:after ~no:failed;
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
          looping st ~continue_:test ~break_:after ~depth (fun () -> block_into st body None);
          close_scope st names;
          finish st.b (Goto test);
          start st.b after
      | For { pattern; iteration; body; mode; _ } ->
          for_each st ~origin:node.origin
            ~schedule:(if mode = Parallel_loop then Chunked else Sequential)
            ~iteration
            ~each:(fun value ->
              match_patterns st [ (pattern, value) ] ~failed:(block st.b);
              block_into st body None)
      | Yield { mode; part } -> (
          let lends =
            match part with
            | Value ({ kind = Construct _; _ } as built) when Core_walk.lent_places part <> [] ->
                Some built
            | _ -> None
          in
          match st.frame.on_yield with
          | Some on_yield ->
              let place =
                match (lends, part, st.frame.yield_into) with
                | Some built, _, _ -> lending st mode built
                | None, Value value, Some slot ->
                    into st value slot;
                    slot
                | None, _, _ -> operand_place st part
              in
              let owned =
                mode = Own || (lends = None && match part with Value _ -> true | Place _ -> false)
              in
              let resume = block st.b and stop = block st.b in
              on_yield place ~owned ~resume ~stop;
              (* On the [stop] path the loop is leaving, so the method drops
                 what it owns and ends. *)
              start st.b stop;
              (match st.frame.exit with
              | Some (exit, depth) ->
                  leave_to st depth;
                  finish st.b (Goto exit)
              | None -> finish st.b Unreachable);
              start st.b resume
          | None when st.pulling ->
              (* In the pulled version of a method a [yield] stays in the
                 code, and yield lowering makes it a state of the cursor.
                 [next] gives its caller a value of its own: a value the
                 method made, or a copy of a place it yields. *)
              let ty = yielded_type_of_frame st in
              let value =
                match (lends, part) with
                | Some _, _ when mode = Mut ->
                    unsupported ~at:(site_of st node.origin)
                      "a cursor over a method that lends places to be changed"
                | Some built, _ -> copied st built
                | None, Value value -> value_place st value
                | None, Place source when trivial st ty -> place st source
                | None, Place source ->
                    let copy = temporary st ty in
                    Glue.copy_into st.context.glue st.b ~destination:copy ~source:(place st source)
                      ty;
                    copy
              in
              let resume = block st.b and stop = block st.b in
              finish st.b (Yield { value = owned st value ty; resume; stop = Some stop });
              (* On the [stop] path the cursor is dropped before it ended, so
                 the method drops what it owns and returns. *)
              start st.b stop;
              leave_to st 0;
              finish st.b (Return None);
              start st.b resume
          | None -> bug "a yield outside a yielding method"))

(* Falls through where the value at a place matches a pattern, and goes to
   [failed] where it does not. Binds nothing and moves nothing. *)
and test_pattern st (pattern : Core.pattern) (place : Lir.place) ~failed =
  let require (condition : Lir.rvalue) =
    let holds = local st.b (Raw Bool) and matched = block st.b in
    emit st.b (Assign (at holds, condition));
    Lir_builder.branch st.b (Copy (at holds)) ~yes:matched ~no:failed;
    start st.b matched
  in
  match pattern.kind with
  | Wildcard | Bind _ -> ()
  | Literal value -> require (Binary (Equal, Copy place, operand st value))
  | Range { start = low; stop = high; inclusive } ->
      require (Binary (Greater_equal, Copy place, operand st low));
      require (Binary ((if inclusive then Less_equal else Less), Copy place, operand st high))
  | Equal_to { value; equal } ->
      let result = temporary st st.context.bool in
      call_with_places st equal [ place; value_place st value ] ~destination:result;
      require (Use (Copy result))
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

(* Inlines a lending or yielding method with its parameters bound to
   [arguments], each by its parameter's index. Each [yield] in the method
   calls [on_yield]. A parameter with no argument takes its default,
   evaluated here. *)
and inline ?yield_into st path type_arguments ~arguments ~call_site ~on_yield =
  if List.exists (Path.equal path) st.frame.inlined then
    unsupported ~at:call_site "%s, which lends through a call to itself" (Path.show path);
  let parameters, body = body_of st.context path in
  let exit = block st.b in
  let caller = st.frame in
  st.frame <-
    {
      code = code_of st.context path type_arguments;
      bindings = Hashtbl.create 16;
      synthetic = Hashtbl.create 4;
      self_place = None;
      on_yield = Some on_yield;
      yield_into;
      inlined = path :: caller.inlined;
      reported =
        (if Path.package path = Path.standard_package then
           Some (Option.value caller.reported ~default:call_site)
         else None);
      exit = Some (exit, List.length st.scopes);
    };
  in_scope st (fun () ->
      List.iteri
        (fun index (parameter : Core.parameter) ->
          let place =
            match (List.find_opt (fun (i, _, _, _) -> i = index) arguments, parameter.default) with
            | Some (_, _, _, place), _ -> place
            | None, Some default ->
                (* The method owns a default's value and drops it, whatever
                   the parameter's mode. *)
                let place = binding st (ground st parameter.type_) in
                in_statement st (fun () -> into st default place);
                place
            | None, None -> bug "%s is given no argument for parameter %d" (Path.show path) index
          in
          bind_local st parameter.local place)
        parameters;
      block_into st body None);
  finish st.b (Goto exit);
  start st.b exit;
  st.frame <- caller

(* Inlines a lending method up to its [yield] and returns the place it
   lends. What is left of the method, its code after the [yield] and the
   drops of what it owns, runs as the caller's statement ends, on every way
   out of it, so the innermost scope owns the lend. Where nothing is left,
   as for an index into a [List], the method ends at its [yield]. *)
and inline_lending st path type_arguments ~arguments ~call_site : Lir.place =
  let _, body = body_of st.context path in
  let several = Method_yields.count body > 1 in
  let depth = List.length st.scopes in
  let goes_on = block st.b in
  (* A method with a [yield] on each of several paths lends whichever it
     reaches, so the caller reads through the address of what was lent,
     and the method goes on from the [yield] it reached. *)
  let ty = yielded_type st path type_arguments in
  let through =
    if several && not (is_zero_size st ty) then
      let writable =
        match (signature_of st.context path).output with Lends (Mut, _) -> true | _ -> false
      in
      Some (local st.b (Pointer { target = Value ty; writable }), writable)
    else None
  in
  let reached = local st.b (Raw (Integer UInt32)) in
  let lent = ref None and waiting = ref [] in
  (* What the method's own scopes owned at a [yield] that the caller went
     on from. *)
  let owned_at_a_yield = ref [] in
  (* A value the method makes to lend is the caller's statement's to drop,
     after the method has gone on, whichever [yield] made it. *)
  let yield_into = if several then Some (temporary st ty) else None in
  inline ?yield_into st path type_arguments ~arguments ~call_site
    ~on_yield:(fun place ~owned:_ ~resume ~stop:_ ->
      (match through with
      | Some (pointer, writable) ->
          emit st.b (Assign (at pointer, Use (Address { place; writable })));
          lent := Some (at pointer / Deref)
      | None -> lent := Some place);
      let scopes = List.filteri (fun i _ -> List.length st.scopes - i > depth) st.scopes in
      let owns_nothing = List.for_all (fun (scope : scope) -> scope.owned = []) scopes in
      if (not several) && Method_yields.each_is_last body && owns_nothing then
        finish st.b (Goto resume)
      else begin
        List.iter
          (fun (scope : scope) ->
            List.iter
              (function
                | Drop_value place when not (List.mem place !owned_at_a_yield) ->
                    owned_at_a_yield := place :: !owned_at_a_yield
                | _ -> ())
              scope.owned)
          scopes;
        emit st.b
          (Assign (at reached, Use (Constant (Integer (UInt32, Z.of_int (List.length !waiting))))));
        waiting := resume :: !waiting;
        finish st.b (Goto goes_on)
      end);
  (match List.rev !waiting with
  | [] -> ()
  | resumes ->
      let resume =
        match resumes with
        | [ only ] -> only
        | _ ->
            let chosen = block st.b in
            in_block st.b chosen (fun () ->
                finish st.b
                  (Switch
                     {
                       value = Copy (at reached);
                       cases = List.mapi (fun index resume -> (Z.of_int index, resume)) resumes;
                       default = None;
                     }));
            chosen
      in
      let scope = innermost_scope st in
      scope.owned <-
        Finish_lend
          {
            resume;
            finished = current st.b;
            selector = local st.b (Raw (Integer UInt32));
            ways = [];
            owned = !owned_at_a_yield;
          }
        :: scope.owned;
      start st.b goes_on);
  match !lent with
  | Some place -> place
  | None when Method_yields.count body = 0 ->
      (* The method has no [yield], so it never returns, and the code after
         the call never runs. The place is never read. *)
      temporary st ty
  | None -> bug "a lending method that lends nothing"

(* Fills in each parameter whose argument the caller omitted, as the bits
   of [mask] say, by evaluating the default inside the function, so that
   changing a default compiles only the function again. An [own] parameter
   with a default may arrive holding nothing, so the function does not own
   it as it arrives: its name is bound to a local the function owns, which
   takes the argument or the default. A parameter that is a view is pointed
   at the default's value, or given its bits, and the function owns that
   value. *)
and fill_defaults st mask (parameters : Core.parameter list) =
  let b = st.b in
  let defaulted =
    List.filter_map
      (fun (parameter : Core.parameter) ->
        Option.map (fun default -> (parameter, default)) parameter.default)
      parameters
  in
  List.iteri
    (fun bit ((parameter : Core.parameter), (default : Core.expression)) ->
      let ty = ground st parameter.type_ in
      let passed = local b (Raw (Integer UInt64)) and is_passed = local b (Raw Bool) in
      emit b
        (Assign
           ( at passed,
             Binary (Bit_and, Copy (at mask), constant_int UInt64 (Z.shift_left Z.one bit)) ));
      emit b
        (Assign (at is_passed, Binary (Not_equal, Copy (at passed), constant_int UInt64 Z.zero)));
      let arrived = local_place st parameter.local in
      let fill = block b and after = block b in
      let unless_passed other = Lir_builder.branch b (Copy (at is_passed)) ~yes:other ~no:fill in
      let pulled what =
        if st.pulling then
          unsupported ~at:(site_of st default.origin)
            "a default for %s, %s, in a yielding method that is pulled" parameter.name what
      in
      if parameter.mode = Own && not (trivial st ty) then begin
        let owned_here = binding st ~name:parameter.name ty in
        bind_local st parameter.local owned_here;
        let passed_block = block b in
        unless_passed passed_block;
        start b passed_block;
        emit b (Assign (owned_here, Use (Move arrived)));
        finish b (Goto after);
        start b fill;
        in_statement st (fun () -> into st default owned_here)
      end
      else begin
        unless_passed after;
        start b fill;
        in_statement st (fun () ->
            match arrived with
            | { projections = [ Deref ]; root = Local pointer } ->
                pulled "which is passed by address";
                let value = binding st ty in
                into st default value;
                emit b (Assign (at pointer, Use (Address { place = value; writable = true })))
            | place when not (trivial st ty) ->
                pulled "which is a view";
                let value = binding st ty in
                into st default value;
                emit b (Assign (place, Use (Copy value)))
            | place -> into st default place)
      end;
      finish b (Goto after);
      start b after)
    defaulted
