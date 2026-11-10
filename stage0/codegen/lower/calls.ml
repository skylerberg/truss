(* Calls: what a call reaches, its arguments evaluated and passed, inlined
   lending and yielding methods, defaults, and the [requires] checks of a
   checked build. *)

open Definitions
open Lowering
open Targets
open Matching
open Lir_builder

let block_into st = !Forward.block_into st
let branch st = !Forward.branch st
let expression st = !Forward.expression st
let into st = !Forward.into st
let operand st = !Forward.operand st
let operator st = !Forward.operator st
let place_expression st = !Forward.place_expression st
let statement st = !Forward.statement st

(* The instance a call to a function or a trait method reaches. *)
let rec resolve_callee st (call_ : C.call) =
  match call_.callee with
  | Trait_method { evidence = Dynamic | Built_in; _ } -> None
  | Function { path; type_arguments } ->
      Some
        ( path,
          List.map
            (Monomorphic.ground_argument st.context.monomorphic st.frame.code.substitution)
            type_arguments )
  | Trait_method { trait; name; receiver; self_type; type_arguments; evidence } -> (
      match trait_method_key st ~trait ~name ~receiver ~self_type ~type_arguments ~evidence with
      | Code { path; type_arguments } -> Some (path, type_arguments)
      | _ -> None)
  | _ -> None

(* Whether a call is to a lending method. *)
and lends st (call_ : C.call) =
  match resolve_callee st call_ with
  | Some (path, _) -> (
      match (signature_of st.context path).output with Lends _ -> true | _ -> false)
  | None -> false

and call_expressions (call_ : C.call) (callee : S.expression) (arguments : S.argument list) =
  let expressions = List.map (fun (a : S.argument) -> a.value) arguments in
  match (call_.callee, callee.kind) with
  | Trait_method { receiver = Read | Mut | Own; _ }, Member (receiver, _)
  | Function { path = Method { receiver = Read | Mut | Own; _ }; _ }, Member (receiver, _) ->
      receiver :: expressions
  | _ -> expressions

and lending_intrinsic st (e : S.expression) =
  match st.frame.code.checked.calls.(e.id) with
  | Some { callee = Intrinsic { operation = Storage_at | Storage_at_mut | View_at; _ }; _ } -> true
  | _ -> false

(* A call's arguments with its receiver, which the checked form does not
   list: the first expression, in the mode the method takes [self] in. *)
and with_receiver st (call_ : C.call) ~(expressions : S.expression list)
    (arguments : C.argument list) =
  let receiver : Path.receiver =
    match call_.callee with
    | Trait_method { receiver; evidence = Dynamic; _ } -> receiver
    | _ -> (
        match resolve_callee st call_ with
        | Some (Method { receiver; _ }, _) -> receiver
        | _ -> Static)
  in
  match (receiver, expressions) with
  | (Read | Mut | Own), first :: _
    when not (List.exists (fun (a : C.argument) -> a.parameter = 0) arguments) ->
      let mode : T.mode = match receiver with Mut -> Mut | Own -> Own | _ -> Read in
      { C.expression = first.id; parameter = 0; mode; conversion = None } :: arguments
  | _ -> arguments

(* The one implicit conversion: a [List] passed where a [Slice] is wanted,
   or a [String] where a [StringSlice] is, becomes a view of it without
   copying, from two of its storage's three fields. *)
and convert st (argument : C.argument) place ty =
  match argument.conversion with
  | Some Owned_to_view -> (
      let view_path (path : Path.t) : Path.t =
        match path with
        | Top { module_ = { package = "standard"; modules = [ "list" ] } as m; name = "List" } ->
            Top { module_ = m; name = "Slice" }
        | Top { module_ = { package = "standard"; modules = [ "text" ] } as m; name = "String" } ->
            Top { module_ = m; name = "StringSlice" }
        | _ -> bug "a view of %s" (Path.show path)
      in
      match ty with
      | Ground.Named { path; arguments } -> (
          let view_ty = Ground.Named { path = view_path path; arguments } in
          match
            ( Monomorphic.shape st.context.monomorphic ty,
              Monomorphic.shape st.context.monomorphic view_ty )
          with
          | Record [ (storage_field, _) ], Record [ (view_field, Typed view) ] ->
              let viewed = new_local st view_ty in
              emit st.b
                (Assign
                   ( viewed / Field view_field,
                     Build
                       {
                         ty = view;
                         variant = None;
                         fields =
                           [
                             ("elements", Copy (place / Field storage_field / Field "buffer"));
                             ("length", Copy (place / Field storage_field / Field "length"));
                           ];
                       } ));
              (viewed, view_ty)
          | _ -> bug "a view of %s" (Ground.to_string ty))
      | _ -> bug "a view of %s" (Ground.to_string ty))
  | Some From_never | Some Function_widening | None -> (place, ty)
  | Some (To_integer | From_integer) -> bug "a conversion that exists only in specifications"

(* The arguments of a call as places, in parameter order. *)
and evaluate_arguments st ~(expressions : S.expression list) ~(arguments : C.argument list) =
  let by_id id = List.find (fun (e : S.expression) -> e.id = id) expressions in
  let evaluate (argument : C.argument) =
    let e = by_id argument.expression in
    let ty = type_of st e.id in
    let place =
      match argument.mode with
      | Mut | Read -> expression st e
      | Own -> (
          match place_expression st e with
          | Some place ->
              let moved = new_local st ty in
              emit st.b (Assign (moved, Use (owned st place ty)));
              moved
          | None -> expression st e)
    in
    let place, ty = convert st argument place ty in
    (argument.parameter, argument.mode, ty, place)
  in
  List.map evaluate arguments |> List.sort (fun (a, _, _, _) (b, _, _, _) -> Int.compare a b)

(* Inlines a lending or yielding method's body with its parameters bound to
   [arguments], each by its parameter's index, handing each [yield] to
   [on_yield]. A parameter left out is given its default, worked out where
   the method writes it. *)
and inline st path type_arguments ~arguments ~call_site ~on_yield =
  if List.exists (Path.equal path) st.frame.inlined then
    Compiler_bug.unsupported ~at:(at_site call_site) "%s, which lends through a call to itself"
      (Path.show path);
  let code = code_of st.context path type_arguments in
  let exit = block st.b in
  let caller = st.frame in
  let frame =
    {
      code;
      bindings = Hashtbl.create 16;
      self_place = None;
      on_yield = Some on_yield;
      inlined = path :: caller.inlined;
      exit = Some (exit, List.length st.scopes);
    }
  in
  st.frame <- frame;
  in_scope st (fun () ->
      List.iteri
        (fun index (mode, written_ty, (parameter : S.parameter)) ->
          let ty, place, filled =
            match List.find_opt (fun (i, _, _, _) -> i = index) arguments with
            | Some (_, _, ty, place) -> (ty, place, false)
            | None -> (
                let ty = Monomorphic.ground st.context.monomorphic code.substitution written_ty in
                match parameter.kind with
                | Named_parameter { default = Some default; _ } ->
                    let place = new_local st ty in
                    st.temporaries <- [] :: st.temporaries;
                    into st default place;
                    end_statement st;
                    (ty, place, true)
                | _ -> bug "%s is given no argument for parameter %d" (Path.show path) index)
          in
          (match parameter.kind with
          | Self_parameter _ -> frame.self_place <- Some place
          | Named_parameter { name; _ } -> Hashtbl.replace frame.bindings name.id place
          | Parameter_error -> ());
          (* A default is the method's own to drop, whatever the mode. *)
          if (mode = T.Own || filled) && not (trivial st ty) then own_in_scope st place)
        code.parameter_types;
      check_requires st ~call_site;
      block_into st code.body None);
  finish st.b (Goto exit);
  start st.b exit;
  st.frame <- caller

(* The place a lending method lends, by inlining it. The method's body runs
   to its end before the caller uses the place, so stage0 lowers only a
   method that has nothing left to do then: each [yield] is the last thing
   its path does, and what it lends is none of the method's own values,
   which are dropped as its body ends. *)
and lend st call_ ~expressions ~arguments ~span =
  match resolve_callee st call_ with
  | Some (path, type_arguments) -> (
      let call_site = site st span in
      let arguments = evaluate_arguments st ~expressions ~arguments in
      if not (yields_last (code_of st.context path type_arguments).body) then
        unsupported st span "%s, a lending method that does more after its yield" (Path.show path);
      let own_from = local_count st.b in
      let lent = ref None in
      inline st path type_arguments ~arguments ~call_site ~on_yield:(fun place ~resume ~stop:_ ->
          (match place.root with
          | Local local when local >= own_from -> (
              match local_type st.b local with
              | Value ty when not (trivial st ty) ->
                  Compiler_bug.unsupported ~at:(at_site call_site)
                    "%s, a lending method that lends a value it made" (Path.show path)
              | _ -> ())
          | _ -> ());
          lent := Some place;
          finish st.b (Goto resume));
      match !lent with Some place -> place | None -> bug "a lending method that lends nothing")
  | None -> bug "a lending call that is not to a method"

(* Whether each [yield] in a body is the last thing its path does. *)
and yields_last (body : S.block) =
  let rec statement_yields (s : S.statement) =
    match s.kind with
    | Yield _ -> true
    | _ ->
        let found = ref false in
        Syntax_walk.statement_parts
          ~expression:(fun e -> if expression_yields e then found := true)
          ~statement:(fun s -> if statement_yields s then found := true)
          s;
        !found
  and expression_yields (e : S.expression) =
    let found = ref false in
    Syntax_walk.expression_parts
      ~expression:(fun e -> if expression_yields e then found := true)
      ~statement:(fun s -> if statement_yields s then found := true)
      e;
    !found
  in
  let rec last_of_block (block : S.block) =
    match List.rev block.statements with
    | [] -> true
    | last :: before -> (not (List.exists statement_yields before)) && last_statement last
  and last_statement (s : S.statement) =
    match s.kind with
    | Yield _ -> true
    | Expression e -> last_expression e
    | _ -> not (statement_yields s)
  and last_expression (e : S.expression) =
    match e.kind with
    | Parenthesized inner -> last_expression inner
    | Block block -> last_of_block block
    | If { then_; else_; _ } -> (
        last_of_block then_
        &&
        match else_ with
        | None -> true
        | Some (Else block) -> last_of_block block
        | Some (Else_if e) -> last_expression e)
    | Match { arms; _ } -> List.for_all (fun (arm : S.arm) -> last_statement arm.body) arms
    | _ -> not (expression_yields e)
  in
  last_of_block body

and call st (e : S.expression) ~callee ~arguments destination =
  match st.frame.code.checked.calls.(e.id) with
  | Some { callee = Function_value; _ } -> call_function_value st ~callee ~arguments destination
  | Some call_ ->
      let expressions = List.map (fun (a : S.argument) -> a.value) arguments in
      let expressions =
        match (call_.callee, callee.kind) with
        | Trait_method { receiver = Read | Mut | Own; _ }, Member (receiver, _)
        | Function { path = Method { receiver = Read | Mut | Own; _ }; _ }, Member (receiver, _) ->
            receiver :: expressions
        | _ -> expressions
      in
      call_with st call_ ~expressions
        ~arguments:(with_receiver st call_ ~expressions call_.arguments)
        destination ~span:e.span
  | None -> bug "a call with no meaning: %s" (source st e.span)

(* A call whose arguments are [expressions], which the checked form's
   [arguments] say where they go. *)
and call_with st (call_ : C.call) ~(expressions : S.expression list) ~(arguments : C.argument list)
    destination ~span =
  if lends st call_ then
    emit st.b
      (Assign
         ( destination,
           Use (owned st (lend st call_ ~expressions ~arguments ~span) (ground st call_.result)) ))
  else
    let by_id id = List.find (fun (e : S.expression) -> e.id = id) expressions in
    let evaluate (argument : C.argument) =
      let e = by_id argument.expression in
      let ty = type_of st e.id in
      let place =
        match argument.mode with
        | Mut | Read -> expression st e
        | Own -> (
            match place_expression st e with
            | Some place ->
                (* An [own] place moves into a temporary the callee takes. *)
                let moved = new_local st ty in
                emit st.b (Assign (moved, Use (owned st place ty)));
                moved
            | None -> expression st e)
      in
      let place, ty = convert st argument place ty in
      (argument.parameter, argument.mode, ty, place)
    in
    let evaluated = List.map evaluate arguments in
    let in_order = List.sort (fun (a, _, _, _) (b, _, _, _) -> Int.compare a b) evaluated in
    match call_.callee with
    | (Function _ | Trait_method _) when yields_cursor st call_ ->
        (* A yielding method called outside a [for] loop makes a cursor,
           which holds its arguments. *)
        let path, type_arguments = Option.get (resolve_callee st call_) in
        let signature = signature_of st.context path in
        let substitution = bind signature.generics type_arguments in
        let arguments = with_placeholders st signature substitution in_order in
        let passed = List.filter_map (fun (mode, ty, place) -> hold st mode ty place) arguments in
        let mask =
          if has_defaults signature then
            [ constant_int UInt64 (Z.of_int (default_mask signature call_)) ]
          else []
        in
        let evidence = List.map (evidence_of st) (evidence_for substitution signature.uses) in
        (* In the order of the pulled method's parameters: its own, the
           defaults' mask, then the evidence. *)
        let fields =
          List.mapi
            (fun i operand -> (Convention.cursor_parameter i, operand))
            (passed @ mask @ evidence)
        in
        let cursor = Ground.Cursor { method_ = path; type_arguments } in
        emit st.b
          (Assign
             ( destination,
               Build
                 {
                   ty = cursor;
                   variant = None;
                   fields = (Convention.cursor_state, Constant (Integer (UInt32, Z.zero))) :: fields;
                 } ))
    | Trait_method { trait; name; self_type; _ }
      when primitive (ground st self_type)
           && List.mem_assoc name primitive_methods
           && Path.equal trait.trait (core (List.assoc name primitive_methods)) ->
        primitive_method st name (ground st self_type) in_order destination ~span
          ~result:(ground st call_.result)
    | Trait_method { name = "copy"; self_type; evidence = Built_in; _ } -> (
        (* [copy()] from [Copyable], which the compiler implements: the
           type's generated copy. *)
        match in_order with
        | (_, _, _, source) :: _ ->
            Glue.copy_into st.context.glue st.b ~destination ~source (ground st self_type)
        | [] -> bug "copy with no value")
    | Trait_method { name = "next"; self_type; evidence = Built_in; _ }
      when match ground st self_type with Cursor _ -> true | _ -> false -> (
        match (ground st self_type, in_order) with
        | Cursor yielding, (_, _, _, cursor) :: _ -> call_next st yielding cursor destination
        | _ -> bug "next with no cursor")
    | Function { path; type_arguments } ->
        let signature = signature_of st.context path in
        let ground_arguments =
          List.map
            (Monomorphic.ground_argument st.context.monomorphic st.frame.code.substitution)
            type_arguments
        in
        let substitution = bind signature.generics ground_arguments in
        let mask = default_mask signature call_ in
        call_instance st
          (Code { path; type_arguments = ground_arguments })
          ~signature ~substitution
          ~arguments:(with_placeholders st signature substitution in_order)
          ~mask ~destination
    | Trait_method { trait; name; evidence = Dynamic; _ } -> (
        (* Through an [any] value: the entry in its table. *)
        let slot, signature = dynamic_slot st.context trait.trait name in
        let lir_signature, result = any_entry_signature st.context signature in
        match in_order with
        | (_, _, _, any) :: rest ->
            let passed = List.filter_map (fun (_, mode, ty, place) -> pass st mode ty place) rest in
            let evidence = List.map (evidence_of st) (evidence_for [] signature.uses) in
            let target =
              Lir.Table_call
                {
                  table = Copy (any / Field "vtable");
                  value = Copy (any / Field "value");
                  slot;
                  signature = lir_signature;
                }
            in
            emit st.b
              (Call
                 {
                   target;
                   arguments = passed @ evidence;
                   result = Convention.destination result destination;
                 });
            if not lir_signature.returns then unreachable_block st
        | [] -> bug "a call through any with no receiver")
    | Trait_method { trait; name; receiver; self_type; type_arguments; evidence } ->
        let key = trait_method_key st ~trait ~name ~receiver ~self_type ~type_arguments ~evidence in
        let path = match key with Code { path; _ } -> path | _ -> bug "a trait method's key" in
        let type_arguments =
          match key with Code { type_arguments; _ } -> type_arguments | _ -> []
        in
        let signature = signature_of st.context path in
        let substitution = bind signature.generics type_arguments in
        call_instance st key ~signature ~substitution
          ~arguments:(with_placeholders st signature substitution in_order)
          ~mask:(default_mask signature call_) ~destination
    | Constructor { type_ = _; variant; _ } ->
        let ty = ground st call_.result in
        let names = constructor_fields st ty variant in
        let fields =
          List.map
            (fun (parameter, _, field_ty, place) ->
              (List.nth names parameter, owned st place field_ty))
            in_order
        in
        let fields = fields @ field_defaults st ty variant call_.defaults_left_out in
        emit st.b (Assign (destination, Build { ty; variant; fields }))
    | Intrinsic { operation; type_arguments } -> (
        let type_arguments =
          List.filter_map
            (fun a ->
              match
                Monomorphic.ground_argument st.context.monomorphic st.frame.code.substitution a
              with
              | Type ty -> Some ty
              | _ -> None)
            type_arguments
        in
        let intrinsic_arguments =
          List.map
            (fun (_, mode, ty, place) ->
              match (Monomorphic.kind st.context.monomorphic ty, mode) with
              | Storage _, _ -> Intrinsics.Place place
              | _, T.Mut -> Intrinsics.Place place
              | Shape (Record [ ("elements", _); ("length", _) ]), _ -> Intrinsics.Place place
              | _ -> Intrinsics.Value (if mode = T.Own then owned st place ty else Copy place))
            in_order
        in
        match
          Intrinsics.lower ~checks:st.context.checks st.context.env st.b st.context.types operation
            ~type_arguments intrinsic_arguments ~destination:(Some destination) ~site:(site st span)
        with
        | Some lent -> emit st.b (Assign (destination, Use (Copy lent)))
        | None -> ())
    | Function_value -> bug "a call through a function value, which [call] lowers"
    | Capability_method { capability; _ } when Path.equal capability panic_path -> (
        (* [Panic.crash] has no evidence: it ends the process at once. *)
        match in_order with
        | [ (_, _, _, message) ] ->
            ignore
              (Intrinsics.lower ~checks:st.context.checks st.context.env st.b st.context.types Crash
                 ~type_arguments:[] [ Intrinsics.Place message ] ~destination:None
                 ~site:(site st span))
        | _ -> bug "Panic.crash takes one message")
    | Capability_method { capability; name } ->
        let slot, signature = capability_method st.context capability name in
        let lir_signature, result = entry_signature st.context signature in
        let passed = List.filter_map (fun (_, mode, ty, place) -> pass st mode ty place) in_order in
        let evidence = evidence_of st capability in
        let target = Lir.Evidence_call { evidence; slot; signature = lir_signature } in
        emit st.b
          (Call { target; arguments = passed; result = Convention.destination result destination });
        if not lir_signature.returns then unreachable_block st
    | Built_in_operator -> bug "a built-in operator called as a function"

(* A trait method of a built-in type that is a primitive operation, written
   where it is called: arithmetic through its intrinsic, so a checked
   build's overflow and division checks report the caller's position, and
   [equal] and [compare] as the comparisons the standard library's bodies
   make. *)
and primitive_method st name ty in_order destination ~span ~result =
  let values = List.map (fun (_, _, _, place) -> Lir.Copy place) in_order in
  let arithmetic operation =
    ignore
      (Intrinsics.lower ~checks:st.context.checks st.context.env st.b st.context.types operation
         ~type_arguments:[ ty ]
         (List.map (fun v -> Intrinsics.Value v) values)
         ~destination:(Some destination) ~site:(site st span))
  in
  match (name, values) with
  | "add", _ -> arithmetic Add
  | "subtract", _ -> arithmetic Subtract
  | "multiply", _ -> arithmetic Multiply
  | "divide", _ -> arithmetic Divide
  | "remainder", _ -> arithmetic Remainder
  | "negate", _ -> arithmetic Negate
  | "equal", [ left; right ] -> emit st.b (Assign (destination, Binary (Equal, left, right)))
  | "compare", [ left; right ] ->
      let ordering variant = Lir.Build { ty = result; variant = Some variant; fields = [] } in
      let less = local st.b (Raw Bool) and equal = local st.b (Raw Bool) in
      let is_less = block st.b and not_less = block st.b in
      let is_equal = block st.b and greater = block st.b and after = block st.b in
      emit st.b (Assign (at less, Binary (Less, left, right)));
      finish st.b
        (Switch { value = Copy (at less); cases = [ (Z.one, is_less) ]; default = Some not_less });
      start st.b is_less;
      emit st.b (Assign (destination, ordering "Less"));
      finish st.b (Goto after);
      start st.b not_less;
      emit st.b (Assign (at equal, Binary (Equal, left, right)));
      finish st.b
        (Switch { value = Copy (at equal); cases = [ (Z.one, is_equal) ]; default = Some greater });
      start st.b is_equal;
      emit st.b (Assign (destination, ordering "Equal"));
      finish st.b (Goto after);
      start st.b greater;
      emit st.b (Assign (destination, ordering "Greater"));
      finish st.b (Goto after);
      start st.b after
  | _ -> bug "%s is not a primitive operation" name

(* Every parameter's argument, in order: a parameter left to its default
   gets a placeholder, which the function overwrites from its default. *)
and with_placeholders st (signature : T.signature) substitution in_order =
  List.mapi
    (fun index (mode, ty) ->
      match List.find_opt (fun (parameter, _, _, _) -> parameter = index) in_order with
      | Some (_, mode, ty, place) -> (mode, ty, place)
      | None ->
          ( mode,
            Monomorphic.ground st.context.monomorphic substitution ty,
            new_local st (Monomorphic.ground st.context.monomorphic substitution ty) ))
    (interface_parameters signature)

and yields_cursor st (call_ : C.call) =
  match resolve_callee st call_ with
  | Some (path, _) -> (
      match (signature_of st.context path).output with Yields _ -> true | _ -> false)
  | None -> false

(* [next()] on a cursor: the pulled method's state machine. *)
and call_next st (yielding : Ground.yielding) cursor destination =
  let option = cursor_result st.context yielding in
  let cursor_pointer = Lir.Pointer { target = Value (Cursor yielding); writable = true } in
  let target signature = Lir.Direct { function_ = Instance (Cursor_next yielding); signature } in
  let self = Lir.Address { place = cursor; writable = true } in
  let convention = Convention.result st.context.env option in
  emit st.b
    (Call
       {
         target = target (Convention.signature [ cursor_pointer ] convention);
         arguments = [ self ];
         result = Convention.destination convention destination;
       })

and default_mask (signature : T.signature) (call_ : C.call) =
  let defaulted = List.filter (fun (p : T.parameter_info) -> p.has_default) signature.parameters in
  let bits =
    List.mapi
      (fun i (p : T.parameter_info) ->
        if List.mem p.name call_.defaults_left_out then 0 else 1 lsl i)
      defaulted
  in
  List.fold_left ( lor ) 0 bits

(* The values of the fields left to their defaults: each default lowered
   where the type writes it, with the type's own tables. *)
and field_defaults st ty variant left_out =
  if left_out = [] then []
  else
    let path =
      match ty with Named { path; _ } -> path | _ -> bug "defaults of %s" (Ground.to_string ty)
    in
    let key = key_of st.context path in
    let declared =
      match (demand st.context Names.definition key, variant) with
      | Some { kind = Type_definition { body = Fields fields; _ }; _ }, None -> fields
      | Some { kind = Type_definition { body = Variants variants; _ }; _ }, Some name -> (
          match List.find_opt (fun (v : S.variant) -> v.name.text = name) variants with
          | Some { fields = Some fields; _ } -> fields
          | _ -> [])
      | _ -> bug "the definition of %s" (Path.show path)
    in
    let shape =
      match (Monomorphic.shape st.context.monomorphic ty, variant) with
      | Record fields, None -> fields
      | Sum variants, Some name ->
          (List.find (fun (v : Memory_layout.variant_shape) -> v.name = name) variants).fields
      | _ -> []
    in
    let caller = st.frame in
    let type_args = match ty with Named { arguments; _ } -> arguments | _ -> [] in
    let interface =
      match demand st.context Environment.type_interface path with
      | Some i -> i
      | None -> bug "no interface for %s" (Path.show path)
    in
    let code =
      {
        caller.code with
        definition_key = key;
        anchor = path;
        text = text_of st.context key;
        checked = checked_of st.context key;
        substitution = bind interface.type_generics type_args;
      }
    in
    st.frame <- { caller with code; bindings = Hashtbl.create 1; self_place = None };
    let values =
      List.map
        (fun name ->
          let default =
            List.find_map
              (fun (field : S.field) ->
                match field.kind with
                | Field_declaration { name = n; default = Some d; _ } when n.text = name -> Some d
                | _ -> None)
              declared
          in
          let field_ty =
            match List.assoc_opt name shape with Some (Typed t) -> t | _ -> bug "no field %s" name
          in
          match default with
          | Some d ->
              let value = new_local st field_ty in
              into st d value;
              (name, owned st value field_ty)
          | None -> bug "no default for %s" name)
        left_out
    in
    st.frame <- caller;
    values

(* A call through a function value: its code, given its environment first,
   then the arguments by position. *)
and call_function_value st ~(callee : S.expression) ~(arguments : S.argument list) destination =
  let f =
    match type_of st callee.id with
    | Function f -> f
    | ty -> bug "a call of %s" (Ground.to_string ty)
  in
  let value = expression st callee in
  let signature = Convention.function_value st.context.env f in
  let passed =
    List.concat
      (List.map2
         (fun ((mode : Ground.mode), ty) (argument : S.argument) ->
           let types_mode : T.mode = match mode with Read -> Read | Mut -> Mut | Own -> Own in
           let place =
             match (place_expression st argument.value, mode) with
             | Some place, Own ->
                 let moved = new_local st ty in
                 emit st.b (Assign (moved, Use (owned st place ty)));
                 moved
             | Some place, _ -> place
             | None, _ -> expression st argument.value
           in
           Option.to_list (pass st types_mode ty place))
         f.parameters arguments)
    (* Then the evidence for what the function value uses. *)
    @ List.map (evidence_of st) f.uses
  in
  let target = Lir.Indirect { value = Copy value; signature } in
  match f.result with
  | Returns ty ->
      emit st.b
        (Call
           {
             target;
             arguments = passed;
             result = Convention.(destination (result st.context.env ty)) destination;
           });
      if ty = Never then unreachable_block st
  | Yields _ | Lends _ -> bug "a function value that yields"

(* Whether a clause can run: none of it is the mathematical [Integer] of
   specifications, a quantifier, or a conversion to or from one. *)
and executable st (e : S.expression) =
  let runs = ref true in
  let rec visit (e : S.expression) =
    (match e.kind with Quantified _ -> runs := false | _ -> ());
    (match raw_type_of st e.id with Some T.Integer -> runs := false | _ -> ());
    (match e.kind with
    | Binary { left; right; _ } when st.frame.code.checked.calls.(e.id) = None ->
        (* A comparison of the values of two integers runs only when they are
           of one type. *)
        let built_in = function Some (T.Named _ as ty) -> T.is_integer_type ty | _ -> false in
        if
          not (built_in (raw_type_of st left.id) && raw_type_of st left.id = raw_type_of st right.id)
        then runs := false
    | _ -> ());
    (match st.frame.code.checked.calls.(e.id) with
    | Some call_ ->
        if
          List.exists
            (fun (a : C.argument) ->
              match a.conversion with Some (To_integer | From_integer) -> true | _ -> false)
            call_.arguments
        then runs := false
    | None -> ());
    if !runs then Syntax_walk.children visit e
  in
  visit e;
  !runs

(* In a checked build, tests each [requires] clause that can run on entry
   to the code, its parameters bound, and panics with the clause when one
   does not hold, at [call_site] for inlined code and at the clause
   otherwise. Stage0's builds keep these whether or not the proofs are
   done, so a test catches a call that breaks a contract as it runs. *)
and check_requires ?call_site st =
  if st.context.checks then
    List.iter
      (fun (clause : S.expression) ->
        if executable st clause then begin
          let holds = block st.b and broken = block st.b in
          let scope = open_scope st in
          branch st clause ~yes:holds ~no:broken;
          start st.b broken;
          let message = "requirement not met: requires " ^ source st clause.span in
          finish st.b
            (Fail
               {
                 failure = Panic;
                 message = Constant (Bytes message);
                 length = usize (String.length message);
                 site = (match call_site with Some s -> s | None -> site st clause.span);
               });
          start st.b holds;
          close_scope st scope
        end)
      st.frame.code.requires

(* Fills in each parameter whose default the caller left out, as the bits
   of [mask] say, from the default's expression, so that changing a default
   compiles only the function again. A parameter that arrives as a pointer
   is pointed at the default's value instead. *)
and fill_defaults st mask =
  let b = st.b in
  let code = st.frame.code in
  let defaulted =
    List.filter_map
      (fun (mode, ty, (parameter : S.parameter)) ->
        match parameter.kind with
        | Named_parameter { name; default = Some default; _ } -> Some (mode, ty, name, default)
        | _ -> None)
      code.parameter_types
  in
  List.iteri
    (fun bit (mode, ty, (name : S.name), default) ->
      let ty = Monomorphic.ground st.context.monomorphic code.substitution ty in
      let passed = local b (Raw (Integer UInt64)) and given = local b (Raw Bool) in
      emit b
        (Assign
           ( at passed,
             Binary (Bit_and, Copy (at mask), constant_int UInt64 (Z.shift_left Z.one bit)) ));
      emit b (Assign (at given, Binary (Not_equal, Copy (at passed), constant_int UInt64 Z.zero)));
      let fill = block b and after = block b in
      finish b (Switch { value = Copy (at given); cases = [ (Z.one, after) ]; default = Some fill });
      start b fill;
      st.temporaries <- [] :: st.temporaries;
      (match Hashtbl.find_opt st.frame.bindings name.id with
      | Some ({ projections = [ Deref ]; root = Local pointer } : Lir.place) ->
          if st.pulling then
            unsupported st (default : S.expression).span
              "a default for %s, which is passed by address, in a yielding method that is pulled"
              name.text;
          let value = new_local st ty in
          into st default value;
          if not (trivial st ty) then own_in_scope st value;
          emit b (Assign (at pointer, Use (Address { place = value; writable = true })))
      | Some place when mode <> T.Own && not (trivial st ty) ->
          if st.pulling then
            unsupported st (default : S.expression).span
              "a default for %s, which is a view, in a yielding method that is pulled" name.text;
          (* The parameter is a view: of the caller's value, or of the
             default, which the function owns, and drops only where it made
             one. *)
          let value = new_local st ty in
          into st default value;
          own_in_scope st value;
          emit b (Assign (place, Use (Copy value)))
      | Some place -> into st default place
      | None -> ());
      st.temporaries <- List.tl st.temporaries;
      finish b (Goto after);
      start b after)
    defaulted
