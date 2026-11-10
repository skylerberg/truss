(* Lowering a function's body from its core form.

   The core form says what the type checker decided, so nothing here looks a
   name up, asks what an operator means, or tells a place from a value by
   its shape. It lowers the nodes it knows, and says [Not_ported] of a body
   that holds any other, which is then lowered from the syntax tree as
   before. *)

open Definitions
open Lowering
open Targets
open Lir_builder

(* What a body holds that is not lowered from the core form yet. *)
exception Not_ported of string

let not_ported what = raise (Not_ported what)

let spans st =
  match demand st.context Names.spans st.frame.code.definition_key with
  | Some spans -> spans
  | None -> bug "no spans for %s" (Path.show st.frame.code.anchor)

(* Where a node is, for a failure to report: the place of the syntax it came
   from. *)
let site_of st (origin : Core.origin) = site st (spans st).(origin)

let local_place st (local : Core.local) : Lir.place =
  let found = function Some place -> place | None -> bug "a name that nothing binds" in
  match local with
  | Named id -> found (Hashtbl.find_opt st.frame.bindings id)
  | Self -> found st.frame.self_place
  | Synthetic number -> found (Hashtbl.find_opt st.frame.made number)

let bind_local st (local : Core.local) place =
  match local with
  | Named id -> Hashtbl.replace st.frame.bindings id place
  | Synthetic number -> Hashtbl.replace st.frame.made number place
  | Self -> bug "a pattern that binds self"

(* The kinds of node that are lowered only from the syntax tree, by name. *)
let expression_kind : Core.kind -> string = function
  | Interpolated _ -> "an interpolated string"
  | Template _ -> "a tagged string"
  | Copy _ -> "a copy"
  | Function_value _ -> "a function as a value"
  | Generic_value _ -> "a generic value"
  | Lambda _ -> "a lambda"
  | Collection_literal _ | Map_literal _ -> "a collection literal"
  | Record_update _ -> "a record with fields replaced"
  | Slice _ -> "a slice"
  | Matches _ -> "a test against a pattern"
  | Cursor_next _ -> "the next part of a cursor"
  | Convert _ -> "a conversion"
  | To_any _ -> "a value made any"
  | Match _ -> "a match"
  | Provide _ -> "a provide"
  | Break | Continue -> "a break or a continue"
  | Todo -> "a todo"
  | Unreachable -> "an unreachable"
  | Echo _ -> "an echo"
  | _ -> "an expression of a specification"

let statement_kind : Core.statement_kind -> string = function
  | Let _ -> "a let with a pattern or an else"
  | Compound_assign _ -> "a compound assignment"
  | For _ -> "a for loop"
  | While _ -> "a while loop"
  | Parallel _ -> "a parallel block"
  | Proof _ -> "a proof block"
  | Yield _ -> "a yield"
  | Evaluate _ | Assign _ | Assert _ -> "a statement"

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
  | Dynamic -> not_ported "a call through an any value"

let rec place st (found : Core.place) : Lir.place =
  match found with
  | Local local -> local_place st local
  | Field { base; field; _ } -> place st base / Field field
  | Temporary value -> value_place st value
  | Lent _ -> not_ported "a part that a call lends"

(* A value worked out into a place of its own, which lasts the statement. *)
and value_place st (value : Core.expression) : Lir.place =
  let ty =
    match value.kind with
    (* It never gives a value, so what it is written into is never read. *)
    | Return _ -> Monomorphic.builtin Unit
    | _ -> ground st value.type_
  in
  let made = temporary st ty in
  into st value made;
  made

and operand st (value : Core.expression) : Lir.operand =
  match value.kind with
  | Integer number -> constant_of st (ground st value.type_) (Integer_value number)
  | Float number -> constant_of st (ground st value.type_) (Float_value number)
  | Boolean truth -> Constant (Bool truth)
  | _ -> Copy (value_place st value)

and into st (value : Core.expression) (destination : Lir.place) =
  let ty = ground st value.type_ in
  let assign rvalue = emit st.b (Assign (destination, rvalue)) in
  match value.kind with
  | Integer _ | Float _ | Boolean _ -> assign (Use (operand st value))
  | Use found -> take st (place st found) ty ~destination
  | String text ->
      let field, storage_ty, storage = string_value st ty text in
      let built = temporary st storage_ty in
      emit st.b (Assign (built, storage));
      assign (Build { ty; variant = None; fields = [ (field, Move built) ] })
  | Constant path -> take st (Matching.static_constant st path) ty ~destination
  | Construct { variant; fields } ->
      let fields =
        List.map
          (fun (name, (given : Core.expression option)) ->
            match given with
            | None -> not_ported "a field left to its default"
            | Some given -> (name, owned st (value_place st given) (ground st given.type_)))
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
  | And _ | Or _ ->
      (* A condition's value: whether its jumps reach [yes]. *)
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
  | Block inner -> block_into st inner (Some destination)
  | Return returned -> return_ st returned
  | kind -> not_ported (expression_kind kind)

(* A call's arguments, one for each of the callee's parameters, each where
   its value is: a place that is lent stays where it is, and a value is
   worked out into a place of its own. A parameter left to its default gets
   a place that holds nothing, and no bit in the mask of defaults passed. *)
and arguments st (signature : T.signature) substitution (given : Core.argument list) =
  let parameters = interface_parameters signature in
  if List.length parameters <> List.length given then
    bug "a call with %d arguments for %d parameters" (List.length given) (List.length parameters);
  let own = List.length parameters - List.length signature.parameters in
  let mask = ref 0 and defaulted = ref 0 in
  let passed =
    List.mapi
      (fun index ((mode, ty), (argument : Core.argument)) ->
        let ty = Monomorphic.ground st.context.monomorphic substitution ty in
        let bit =
          if index >= own && (List.nth signature.parameters (index - own)).has_default then begin
            incr defaulted;
            Some (!defaulted - 1)
          end
          else None
        in
        match argument with
        | Default -> (mode, ty, temporary st ty)
        | Passed { value; _ } -> (
            Option.iter (fun bit -> mask := !mask lor (1 lsl bit)) bit;
            ( mode,
              ty,
              match value with Place found -> place st found | Value value -> value_place st value
            )))
      (List.combine parameters given)
  in
  if !defaulted > 62 then
    Compiler_bug.unsupported "a function with more than 62 parameters that have defaults";
  (passed, !mask)

and call_into st (value : Core.expression) (call : Core.call) destination =
  if call.lends <> None then not_ported "a call that lends";
  let instance key path type_arguments =
    let signature = signature_of st.context path in
    (match signature.output with
    | Returns _ -> ()
    | Yields _ | Lends _ -> not_ported "a call of a method that yields");
    let substitution = bind signature.generics type_arguments in
    let passed, mask = arguments st signature substitution call.arguments in
    call_instance st key ~signature ~substitution ~arguments:passed ~mask ~destination
  in
  match call.callee with
  | Function { path; type_arguments } ->
      let type_arguments =
        List.map
          (Monomorphic.ground_argument st.context.monomorphic st.frame.code.substitution)
          type_arguments
      in
      instance (Code { path; type_arguments }) path type_arguments
  | Trait_method { trait; name; receiver; self_type; type_arguments; evidence = found } -> (
      match
        trait_method_key st ~trait ~name ~receiver ~self_type ~type_arguments
          ~evidence:(evidence found)
      with
      | Code { path; type_arguments } as key -> instance key path type_arguments
      | _ -> bug "a trait method's key")
  | Intrinsic { operation; type_arguments } -> (
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
      let given =
        List.map
          (fun (argument : Core.argument) ->
            match argument with
            | Passed { value = Place found; _ } -> Intrinsics.Place (place st found)
            | Passed { mode; value = Value inner } ->
                let ty = ground st inner.type_ in
                let made = value_place st inner in
                (* An operation on storage or a view reads it where it is. *)
                if Storage.elements_of ty <> None || Storage.viewed ty <> None then
                  Intrinsics.Place made
                else Intrinsics.Value (if mode = T.Own then owned st made ty else Copy made)
            | Default -> bug "an operation of the compiler with a default")
          call.arguments
      in
      match
        Intrinsics.lower ~checks:st.context.checks st.context.env st.b st.context.types operation
          ~type_arguments given ~destination:(Some destination) ~site:(site_of st value.origin)
      with
      | Some _ -> not_ported "an operation that lends"
      | None -> ())
  | Capability_method _ -> not_ported "a call of a capability's method"
  | Indirect _ -> not_ported "a call through a function value"

and return_ st (returned : Core.expression option) =
  (match st.frame.exit with
  | Some _ -> not_ported "a return from a method written into its caller"
  | None -> ());
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

(* A condition as jumps: to [yes] when it holds, and to [no] when it does
   not. *)
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
  | Matches _ -> not_ported "a test against a pattern"
  | _ ->
      let value = operand st condition in
      finish st.b (Switch { value; cases = [ (Z.one, yes) ]; default = Some no })

and block_into st (inner : Core.block) destination =
  in_scope st (fun () ->
      List.iter (statement st) inner.statements;
      match (inner.value, destination) with
      | Some value, Some destination ->
          in_statement st (fun () ->
              (* An early [return] writes the result too, and where its path
                 and this one meet again the slot may read as written. *)
              if Some destination = result_place st then clear_result st;
              into st value destination)
      | Some value, None -> in_statement st (fun () -> ignore (value_place st value))
      | None, _ -> ())

and statement st (written : Core.statement) =
  in_statement st (fun () ->
      match written.kind with
      | Evaluate { kind = Use found; _ } -> ignore (place st found)
      | Evaluate value -> ignore (value_place st value)
      | Let { pattern = { kind = Wildcard; _ }; value; else_ = None } -> (
          match value with
          | Place found -> ignore (place st found)
          | Value value -> ignore (value_place st value))
      | Let
          {
            pattern = { kind = Bind { local; name; mutable_; _ }; type_; _ };
            value;
            else_ = None;
          } -> (
          let ty = ground st type_ in
          match value with
          | Place found when (not mutable_) && not (trivial st ty) ->
              (* A [let] of a place views it. *)
              bind_local st local (Statements.snapshot st (place st found))
          | Place found ->
              let held = binding st ~name ty in
              take st (place st found) ty ~destination:held;
              bind_local st local held
          | Value value ->
              let held = binding st ~name ty in
              into st value held;
              bind_local st local held)
      | Assign { target; value } ->
          (* The new value is worked out into a place of its own, which
             nothing else names, before it replaces the old one. *)
          let ty = ground st value.type_ in
          let target = place st target in
          let fresh = temporary st ty in
          into st value fresh;
          replace st target ty ~by:fresh
      | Assert { value; _ } ->
          let held = operand st value in
          let failed = block st.b and after = block st.b in
          finish st.b (Switch { value = held; cases = [ (Z.one, after) ]; default = Some failed });
          start st.b failed;
          let message = "assert " ^ source st (spans st).(value.origin) in
          finish st.b
            (Fail
               {
                 failure = Assertion;
                 message = Constant (Bytes message);
                 length = usize (String.length message);
                 site = site_of st written.origin;
               });
          start st.b after
      | kind -> not_ported (statement_kind kind))

(* Writes the body of the function a state is entered for into its result.
   Where the body holds what is lowered only from the syntax tree, nothing
   written is to be kept, and the error says what it holds. *)
let body st (form : Core.t) : (unit, string) result =
  match form.parts with
  | Function { body = Some inner; _ } | Test inner -> (
      match block_into st inner (result_place st) with
      | () -> Ok ()
      | exception Not_ported what -> Error what)
  | _ -> Error "a definition that has no body"
