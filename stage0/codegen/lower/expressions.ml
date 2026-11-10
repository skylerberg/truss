(* Expressions: the place an expression names or a temporary holding its
   value, and an expression written into a destination. *)

open Definitions
open Lowering
open Targets
open Calls
open Values
open Lir_builder

let block_into st = !Forward.block_into st
let branch st = !Forward.branch st
let if_ st = !Forward.if_ st
let match_ st = !Forward.match_ st

let rec expression st (e : S.expression) : Lir.place =
  match e.kind with
  | Parenthesized inner | Mode (_, inner) -> expression st inner
  | Todo | Unreachable | Return _ | Break | Continue ->
      (* These never give a value, so what they are written into is never
         read. *)
      let nowhere = new_local st (Monomorphic.builtin Unit) in
      into st e nowhere;
      nowhere
  | Name _ | Member _ | Self_value | Bracket _ | Call _ -> (
      (* An index or a lending call names a place, as a name does. *)
      match place_expression st e with
      | Some place -> place
      | None ->
          let destination = temporary st (type_of st e.id) in
          into st e destination;
          destination)
  | _ ->
      let ty = type_of st e.id in
      let destination = temporary st ty in
      into st e destination;
      destination

(* The place an expression names, if it names one: a local, a parameter,
   [self], or a field of one. *)
and place_expression st (e : S.expression) : Lir.place option =
  match e.kind with
  | Parenthesized inner | Mode (_, inner) -> place_expression st inner
  | Self_value -> st.frame.self_place
  | (Name _ | Member _) when constant_place st e <> None -> constant_place st e
  | Name _ -> (
      match st.frame.code.checked.meanings.(e.id) with
      | Some (Local_value local) -> (
          match Hashtbl.find_opt st.frame.bindings local with
          | Some place -> Some place
          | None -> bug "local %d is not bound" local)
      | _ -> None)
  | Member (base, name) -> (
      match st.frame.code.checked.meanings.(e.id) with
      | Some (Field_read _) ->
          let base = expression st base in
          Some (base / Field name.text)
      | _ -> None)
  | Bracket (base, items) -> (
      match st.frame.code.checked.calls.(e.id) with
      | Some call_ ->
          let expressions =
            base
            :: List.filter_map (function S.Item e -> Some e | Item_constraint _ -> None) items
          in
          let arguments =
            if call_.arguments <> [] then with_receiver st call_ ~expressions call_.arguments
            else
              List.mapi
                (fun i (e : S.expression) ->
                  { C.expression = e.id; parameter = i; mode = Read; conversion = None })
                expressions
          in
          Some (lend st call_ ~expressions ~arguments ~span:e.span)
      | None -> None)
  | Call (_, arguments) when lending_intrinsic st e -> (
      (* [storage_at], [storage_at_mut], and [view_at] lend an element's
         place itself. *)
      match st.frame.code.checked.calls.(e.id) with
      | Some { callee = Intrinsic { operation; type_arguments }; arguments = checked; _ } ->
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
          let expressions = List.map (fun (a : S.argument) -> a.value) arguments in
          let values =
            List.map
              (fun (argument : C.argument) ->
                let e =
                  List.find (fun (x : S.expression) -> x.id = argument.expression) expressions
                in
                (argument.parameter, e))
              checked
            |> List.sort (fun (a, _) (b, _) -> Int.compare a b)
            |> List.map (fun (parameter, e) ->
                if parameter = 0 then Intrinsics.Place (expression st e)
                else Intrinsics.Value (operand st e))
          in
          Intrinsics.lower ~checks:st.context.checks st.context.env st.b st.context.types operation
            ~type_arguments values ~destination:None ~site:(site st e.span)
      | _ -> None)
  | Call (callee, arguments) -> (
      match st.frame.code.checked.calls.(e.id) with
      | Some ({ callee = Function _ | Trait_method _; _ } as call_) when lends st call_ ->
          let expressions = call_expressions call_ callee arguments in
          Some
            (lend st call_ ~expressions
               ~arguments:(with_receiver st call_ ~expressions call_.arguments)
               ~span:e.span)
      | _ -> None)
  | _ -> None

(* A constant's static data, which is a read-only place. *)
and constant_place st (e : S.expression) =
  match st.frame.code.checked.meanings.(e.id) with
  | Some (Global { path; _ }) -> (
      match demand st.context Environment.constant_type path with
      | Some ty ->
          Some { Lir.root = Static { key = Constant path; ty = ground st ty }; projections = [] }
      | None -> None)
  | _ -> None

and operand st (e : S.expression) =
  let ty = type_of st e.id in
  match e.kind with
  | Integer _ | Float _ -> constant_of st ty (literal st e.id)
  | Prefix (Negate, ({ kind = Integer _; _ } as inner))
    when st.frame.code.checked.calls.(e.id) = None ->
      negated_literal st ty inner
  | True -> Constant (Bool true)
  | False -> Constant (Bool false)
  | _ -> Copy (expression st e)

(* Writes the value of an expression to [destination]. *)
and into st (e : S.expression) (destination : Lir.place) =
  let ty () = type_of st e.id in
  let assign rvalue = emit st.b (Assign (destination, rvalue)) in
  match e.kind with
  | Parenthesized inner | Mode (_, inner) -> into st inner destination
  | Integer _ | Float _ -> assign (Use (constant_of st (ty ()) (literal st e.id)))
  | True -> assign (Use (Constant (Bool true)))
  | False -> assign (Use (Constant (Bool false)))
  | String _ when st.frame.code.checked.literals.(e.id) <> None ->
      (* A tagged character, such as [Character"a"] or [UInt8"\n"]: a number. *)
      assign (Use (constant_of st (ty ()) (literal st e.id)))
  | String literal when literal.rest = [] && literal.tag = None ->
      let field, storage_ty, storage = string_value st (ty ()) literal.first.value in
      let built = new_local st storage_ty in
      emit st.b (Assign (built, storage));
      assign (Build { ty = ty (); variant = None; fields = [ (field, Move built) ] })
  | Name _ | Self_value | Member _ -> (
      match place_expression st e with
      | Some place -> assign (Use (owned st place (ty ())))
      | None -> name_value st e destination)
  | Call (callee, arguments) -> call st e ~callee ~arguments destination
  | Binary { operator = And | Or; _ } | Is _ ->
      (* A condition's value: whether its jumps reach [yes]. *)
      in_scope st (fun () ->
          let yes = block st.b and no = block st.b and after = block st.b in
          branch st e ~yes ~no;
          start st.b yes;
          assign (Use (Constant (Bool true)));
          finish st.b (Goto after);
          start st.b no;
          assign (Use (Constant (Bool false)));
          finish st.b (Goto after);
          start st.b after)
  | Binary { left; right; _ } -> operator st e [ left; right ] destination
  | Prefix (Negate, ({ kind = Integer _; _ } as inner))
    when st.frame.code.checked.calls.(e.id) = None ->
      assign (Use (negated_literal st (ty ()) inner))
  | Prefix (Not, inner) when st.frame.code.checked.calls.(e.id) = None || is_built_in st e ->
      assign (Unary (Not, operand st inner))
  | Prefix (_, inner) -> operator st e [ inner ] destination
  | Block block -> block_into st block (Some destination)
  | If { condition; then_; else_ } -> if_ st ~condition ~then_ ~else_ (Some destination)
  | Match { scrutinees; arms } -> match_ st ~scrutinees ~arms (Some destination)
  | Return value ->
      return_ st value;
      ()
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
             site = site st e.span;
           });
      start st.b (block st.b)
  | Unreachable -> unreachable_block st
  | Echo inner ->
      into st inner destination;
      echo st destination (ty ()) e.span
  | List elements -> list_into st (ty ()) elements destination ~span:e.span
  | Try inner -> try_ st inner destination
  | String literal when literal.tag = None -> interpolate st literal destination
  | String literal -> (
      match st.frame.code.checked.templates.(literal.id) with
      | Some template when template.from_template <> None ->
          template_into st literal template destination ~span:e.span
      | _ -> bug "a tagged string with no template")
  | With (base, updates) -> with_ st base updates destination
  | Lambda { parameters; body } -> lambda st e ~parameters ~body destination
  | Bracket _ -> (
      match place_expression st e with
      | Some place -> assign (Use (owned st place (ty ())))
      | None -> bug "an index with no meaning")
  | Any inner -> any_value st e inner destination
  | Map entries ->
      collection_into st (ty ()) destination ~span:e.span
        (List.map
           (fun ((key : S.expression), (value : S.expression)) ->
             [ (key, type_of st key.id); (value, type_of st value.id) ])
           entries)
  | Range { start = Some start; stop = Some stop; inclusive } ->
      (* A [Range] value: its two ends and whether it includes the last. *)
      let end_ (e : S.expression) = owned st (expression st e) (type_of st e.id) in
      let start = end_ start in
      let stop = end_ stop in
      assign
        (Build
           {
             ty = ty ();
             variant = None;
             fields = [ ("start", start); ("stop", stop); ("inclusive", Constant (Bool inclusive)) ];
           })
  | Provide { implementations; body } -> provide st e implementations body destination
  | Range _ -> unsupported st e.span "a range without both of its ends, as a value"
  | Quantified _ -> unsupported st e.span "a quantifier in code that runs"
  | Self_type_value -> bug "Self as a value"
  | Expression_error -> bug "an expression that did not parse"

(* An operator: a call of the trait method or intrinsic the checked form
   chose, with the operands as its arguments in order, or a built-in
   operation on [Bool] or integers. *)
and operator st (e : S.expression) operands destination =
  match st.frame.code.checked.calls.(e.id) with
  | Some { callee = Built_in_operator; _ } -> (
      let operand_values = List.map (operand st) operands in
      let rvalue : Lir.rvalue =
        match (e.kind, operand_values) with
        | Binary { operator; _ }, [ left; right ] ->
            Binary
              ( (match operator with
                | Bit_and -> Bit_and
                | Bit_or -> Bit_or
                | Bit_xor -> Bit_xor
                | Shift_left -> Shift_left
                | Shift_right -> Shift_right
                | Equal -> Equal
                | Not_equal -> Not_equal
                | Less -> Less
                | Less_equal -> Less_equal
                | Greater -> Greater
                | Greater_equal -> Greater_equal
                | _ -> bug "a built-in binary operator"),
                left,
                right )
        | Prefix (Not, _), [ value ] -> Unary (Not, value)
        | Prefix (Complement, _), [ value ] -> Unary (Complement, value)
        | Prefix (Negate, _), [ value ] -> Unary (Negate, value)
        | _ -> bug "a built-in operator"
      in
      match e.kind with _ -> emit st.b (Assign (destination, rvalue)))
  | Some _
    when match (e.kind, operands) with
         | ( Binary { operator = Equal | Not_equal | Less | Less_equal | Greater | Greater_equal; _ },
             [ left; _ ] ) ->
             primitive (type_of st left.id)
         | _ -> false -> (
      (* A comparison of built-in values is a primitive operation, with the
         lawful rules for floats. *)
      match (e.kind, operands) with
      | Binary { operator; _ }, [ left; right ] ->
          let compare : Lir.binary =
            match operator with
            | Equal -> Equal
            | Not_equal -> Not_equal
            | Less -> Less
            | Less_equal -> Less_equal
            | Greater -> Greater
            | _ -> Greater_equal
          in
          emit st.b (Assign (destination, Binary (compare, operand st left, operand st right)))
      | _ -> bug "a comparison")
  | Some call_ -> (
      let arguments =
        List.mapi
          (fun i (operand : S.expression) ->
            { C.expression = operand.id; parameter = i; mode = Read; conversion = None })
          operands
      in
      let arguments = if call_.arguments = [] then arguments else call_.arguments in
      (* A comparison is a call of [equal] or [compare], whose result it
         tests. *)
      let test variant ~negate =
        let ordering =
          new_local st
            (Named
               {
                 path =
                   Top
                     { module_ = { package = "standard"; modules = [ "core" ] }; name = "Ordering" };
                 arguments = [];
               })
        in
        call_with st call_ ~expressions:operands ~arguments ordering ~span:e.span;
        let is = local st.b (Raw Bool) in
        emit st.b (Assign (at is, Is_variant (ordering, variant)));
        emit st.b
          (Assign (destination, if negate then Unary (Not, Copy (at is)) else Use (Copy (at is))))
      in
      match e.kind with
      | Binary { operator = Less; _ } -> test "Less" ~negate:false
      | Binary { operator = Less_equal; _ } -> test "Greater" ~negate:true
      | Binary { operator = Greater; _ } -> test "Greater" ~negate:false
      | Binary { operator = Greater_equal; _ } -> test "Less" ~negate:true
      | Binary { operator = Not_equal; _ } ->
          let equal = new_local st st.context.bool in
          call_with st call_ ~expressions:operands ~arguments equal ~span:e.span;
          emit st.b (Assign (destination, Unary (Not, Copy equal)))
      | _ -> call_with st call_ ~expressions:operands ~arguments destination ~span:e.span)
  | None -> (
      (* A specification's comparison of built-in integers, which is of
         their values, with no call: exact when both are of one type, the
         only case [executable] lets run. *)
      match (e.kind, operands) with
      | Binary { operator; _ }, [ left; right ] ->
          let compare : Lir.binary =
            match operator with
            | Equal -> Equal
            | Not_equal -> Not_equal
            | Less -> Less
            | Less_equal -> Less_equal
            | Greater -> Greater
            | Greater_equal -> Greater_equal
            | _ -> bug "an operator with no call: %s" (source st e.span)
          in
          emit st.b (Assign (destination, Binary (compare, operand st left, operand st right)))
      | _ -> bug "an operator with no call: %s" (source st e.span))
