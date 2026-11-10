(* Lowers a function body from its core form.

   The core form records what the type checker resolved: the callee of each
   call, whether each operand is a place or a value, and every type. So this
   lowering does no name resolution and no type inference. *)

open Definitions
open Lowering
open Targets
open Lir_builder

(* The parameters, the [requires] clauses, and the body of a function or a
   test, from its core form. *)
let body_of context path : Core.parameter list * Core.condition list * Core.block =
  match demand context Infer.core_of_path path with
  | Some ({ definition = Function { parameters; contract; body = Some body }; _ }, _) ->
      (parameters, contract.requires, body)
  | Some ({ definition = Test body; _ }, _) -> ([], [], body)
  | _ -> bug "%s has no body in its core form" (Path.show path)

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
  | Lent { kind = Call call; origin; _ } -> lend st call ~call_site:(site_of st origin)
  | Lent _ -> bug "a lent place that is not a call"

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
  | Construct { variant; fields } ->
      let fields =
        List.map
          (fun (name, (field : Core.operand option)) ->
            match field with
            | Some (Value field) -> (name, owned st (value_place st field) (ground st field.type_))
            | Some (Place _) ->
                Compiler_bug.unsupported "a yielded value with a field that is a lent place"
            | None ->
                (* The default is written in the type's definition, so it is
                   lowered in that definition's frame. *)
                let default = field_default st ty ~variant ~field:name in
                in_type_definition st ty (fun () ->
                    (name, owned st (value_place st default) (ground st default.type_))))
          fields
      in
      assign (Build { ty; variant; fields })
  | Interpolated { pieces; builder_new; builder_write; builder_finish } ->
      (* Each piece is written to one text builder: a literal as it is, and
         a value through its [Display]. *)
      let builder = temporary st (result_type st builder_new) in
      call_with_places st builder_new [] ~destination:builder;
      let text_type = List.nth (parameter_types st builder_write) 1 in
      let discarded callee = temporary st (result_type st callee) in
      List.iter
        (fun (piece : Core.piece) ->
          match piece with
          | Text "" -> ()
          | Text text ->
              let slice = temporary st text_type in
              string_literal st text_type text ~destination:slice;
              call_with_places st builder_write [ builder; slice ]
                ~destination:(discarded builder_write)
          | Displayed { value; display } ->
              call_with_places st display
                [ operand_place st value; builder ]
                ~destination:(discarded display))
        pieces;
      call_with_places st builder_finish [ builder ] ~destination
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
  | Provide { implementations; body } ->
      (* The body runs with the evidence of each implementation added. *)
      let enclosing = st.evidence in
      let added =
        List.concat_map
          (fun (implementation : Core.implementation) ->
            let place = operand_place st implementation.value in
            let pointer =
              if zero_size st (ground st implementation.type_) then Lir.Constant Null
              else Address { place; writable = true }
            in
            provided_evidence st ~implementation:pointer
              (List.map
                 (fun (provided : Core.provided) ->
                   (provided.capability, provided.impl, provided.arguments))
                 implementation.provides))
          implementations
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
        Compiler_bug.unsupported
          ~at:(at_site (site_of st value.origin))
          "a lambda in a yielding method that is pulled";
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
        ~body:(fun inner taken ->
          List.iter2
            (fun pattern (place, _, _) ->
              match_patterns inner [ (pattern, place) ] ~failed:(block inner.b))
            parameters taken;
          block_into inner body (result_place inner))
        destination
  | Slice { call; _ } -> into st call destination
  | Implies _ | Result | Old _ | Quantified _ | Yielded | Finished | Identical _
  | Specification_function _ | Method_time _ ->
      bug "a specification-only expression in code that runs"

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
            ~signature ~substitution ~arguments ~mask ~destination
      | Yields _ ->
          (* A yielding method called outside a [for] loop makes a cursor,
             which holds its arguments. *)
          cursor_into st ~path ~type_arguments ~signature ~substitution ~arguments ~mask destination
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
  | None, Trait_method { trait; name; _ } -> (
      (* Through an [any] value, which is the receiver. *)
      match List.map (argument_place st) call.arguments with
      | (_, _, any) :: arguments ->
          call_through_any st ~trait:trait.trait ~name ~any ~arguments destination
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
            within = None;
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
  | Passed { mode; value } -> (mode, ground st (operand_type value), operand_place st value)
  | Default -> bug "an omitted argument in a call that has no defaults"

(* A loop over the cursor of a yielding method's call: the pulled method's
   [next] is called until it gives [None]. *)
and pull_cursor st (yielding : Ground.yielding) cursor ~pattern ~body =
  pull_loop st
    ~option:(cursor_result st.context yielding)
    ~call_next:(fun destination -> call_next st yielding cursor destination)
    ~body:(fun value ->
      match_patterns st [ (pattern, value) ] ~failed:(block st.b);
      block_into st body None)

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

(* The types of a callee's parameters, in order, a receiver first. *)
and parameter_types st (callee : Core.callee) =
  let _, _, signature, substitution = resolved st callee in
  List.map
    (fun (_, ty) -> Monomorphic.ground st.context.monomorphic substitution ty)
    (interface_parameters signature)

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
    ~signature ~substitution ~arguments ~mask:0 ~destination

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
        | Passed { mode; value = Value value } ->
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
  match st.frame.exit with
  | Some (exit, depth) ->
      (* A [return] in an inlined method ends the method. *)
      Option.iter (fun returned -> ignore (value_place st returned)) returned;
      leave_to st depth;
      finish st.b (Goto exit);
      start st.b (block st.b)
  | None ->
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
      match_patterns st [ (pattern, operand_place st value) ] ~failed:no;
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
      | Parallel statements ->
          (* Stage0 runs the statements of a [parallel] block in order. *)
          List.iter (statement st) statements
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
          looping st ~continue_:test ~break_:after ~depth (fun () -> block_into st body None);
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
              looping st ~continue_:step ~break_:after ~depth (fun () -> block_into st body None));
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
      | For { pattern; iteration = Yielding_call ({ kind = Call call; _ } as iterated); body; _ }
        -> (
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
                  pull_cursor st yielding cursor ~pattern ~body)
          | Some (path, type_arguments) ->
              (match (signature_of st.context path).output with
              | Yields _ -> ()
              | Returns _ | Lends _ -> bug "a loop over %s, which does not yield" (Path.show path));
              let arguments = arguments_to_inline st path type_arguments call.arguments in
              let caller = st.frame in
              let depth = List.length st.scopes in
              let after = block st.b in
              inline st path type_arguments ~arguments ~call_site:(site_of st node.origin)
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
      | For { pattern; iteration = Cursor { cursor; next = None }; body; _ } -> (
          match ground st (Core_walk.place_type cursor) with
          | Cursor yielding -> pull_cursor st yielding (place st cursor) ~pattern ~body
          | cursor_ty -> bug "a loop over %s, which is not a cursor" (Ground.to_string cursor_ty))
      | For { pattern; iteration = Cursor { cursor; next = Some next }; body; _ } ->
          (* A value of a type that implements [Cursor]: its own [next] is
             called until it gives [None]. *)
          let cursor = place st cursor in
          pull_loop st ~option:(result_type st next)
            ~call_next:(fun destination -> call_with_places st next [ cursor ] ~destination)
            ~body:(fun value ->
              match_patterns st [ (pattern, value) ] ~failed:(block st.b);
              block_into st body None)
      | Yield { part; _ } -> (
          match st.frame.on_yield with
          | Some on_yield ->
              let place = operand_place st part in
              let resume = block st.b and stop = block st.b in
              on_yield place ~resume ~stop;
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
                match part with
                | Value value -> value_place st value
                | Place source when trivial st ty -> place st source
                | Place source ->
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
and inline st path type_arguments ~arguments ~call_site ~on_yield =
  if List.exists (Path.equal path) st.frame.inlined then
    Compiler_bug.unsupported ~at:(at_site call_site) "%s, which lends through a call to itself"
      (Path.show path);
  let parameters, requires, body = body_of st.context path in
  let exit = block st.b in
  let caller = st.frame in
  st.frame <-
    {
      code = code_of st.context path type_arguments;
      bindings = Hashtbl.create 16;
      synthetic = Hashtbl.create 4;
      self_place = None;
      on_yield = Some on_yield;
      inlined = path :: caller.inlined;
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
      check_requires st ~call_site requires;
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
  let _, _, body = body_of st.context path in
  if Method_yields.count body > 1 then
    Compiler_bug.unsupported ~at:(at_site call_site) "%s, a lending method with more than one yield"
      (Path.show path);
  let depth = List.length st.scopes in
  let goes_on = block st.b in
  let lent = ref None and waits = ref None in
  inline st path type_arguments ~arguments ~call_site ~on_yield:(fun place ~resume ~stop:_ ->
      lent := Some place;
      let owns_nothing =
        List.for_all
          (fun (scope : scope) -> scope.owned = [])
          (List.filteri (fun i _ -> List.length st.scopes - i > depth) st.scopes)
      in
      if Method_yields.each_is_last body && owns_nothing then finish st.b (Goto resume)
      else begin
        waits := Some resume;
        finish st.b (Goto goes_on)
      end);
  (match !waits with
  | Some resume ->
      let scope = innermost_scope st in
      scope.owned <-
        Finish_lend
          {
            resume;
            finished = current st.b;
            selector = local st.b (Raw (Integer UInt32));
            ways = [];
          }
        :: scope.owned;
      start st.b goes_on
  | None -> ());
  match !lent with
  | Some place -> place
  | None when Method_yields.count body = 0 ->
      (* The method has no [yield], so it never returns, and the code after
         the call never runs. The place is never read. *)
      temporary st (yielded_type st path type_arguments)
  | None -> bug "a lending method that lends nothing"

(* In a checked build, tests each [requires] clause that can run, on entry to
   the code with its parameters bound, and panics with the clause's text
   when one does not hold: at [call_site] for inlined code and at the clause
   otherwise. Stage0's builds keep these checks whether or not the proofs
   are done, so a test catches a call that breaks a contract as it runs. *)
and check_requires ?call_site st (requires : Core.condition list) =
  if st.context.checks then
    List.iter
      (fun (clause : Core.condition) ->
        if clause.executable then begin
          let holds = block st.b and broken = block st.b in
          let scope = open_scope st Bindings in
          branch st clause.value ~yes:holds ~no:broken;
          start st.b broken;
          let message =
            "requirement not met: requires " ^ source st (spans st).(clause.value.origin)
          in
          finish st.b
            (Fail
               {
                 failure = Panic;
                 message = Constant (Bytes message);
                 length = usize (String.length message);
                 site = Option.value call_site ~default:(site_of st clause.value.origin);
               });
          start st.b holds;
          close_scope st scope
        end)
      requires

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
      let passed = local b (Raw (Integer UInt64)) and given = local b (Raw Bool) in
      emit b
        (Assign
           ( at passed,
             Binary (Bit_and, Copy (at mask), constant_int UInt64 (Z.shift_left Z.one bit)) ));
      emit b (Assign (at given, Binary (Not_equal, Copy (at passed), constant_int UInt64 Z.zero)));
      let arrived = local_place st parameter.local in
      let fill = block b and after = block b in
      let unless_given other =
        finish b
          (Switch { value = Copy (at given); cases = [ (Z.one, other) ]; default = Some fill })
      in
      let pulled what =
        if st.pulling then
          Compiler_bug.unsupported
            ~at:(at_site (site_of st default.origin))
            "a default for %s, %s, in a yielding method that is pulled" parameter.name what
      in
      if parameter.mode = Own && not (trivial st ty) then begin
        let owned_here = binding st ~name:parameter.name ty in
        bind_local st parameter.local owned_here;
        let taken = block b in
        unless_given taken;
        start b taken;
        emit b (Assign (owned_here, Use (Move arrived)));
        finish b (Goto after);
        start b fill;
        in_statement st (fun () -> into st default owned_here)
      end
      else begin
        unless_given after;
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
