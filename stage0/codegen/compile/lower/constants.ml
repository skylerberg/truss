(* Constants: a constant's value folded exactly from its expression, or
   computed by running its evaluator. *)

open Definitions
open Lowering
open Targets
open Emit_c.Builder

let ( let* ) = Option.bind

let all values =
  List.fold_right
    (fun value rest ->
      let* value = value in
      let* rest = rest in
      Some (value :: rest))
    values (Some [])

(* An integer of a kind, if the kind holds it. *)
let integer st (kind : Memory_layout.integer) value =
  let low, high = Memory_layout.integer_range (Memory_layout.target st.context.env) kind in
  if Z.leq low value && Z.leq value high then Some (Lowered.Static_scalar (Integer (kind, value)))
  else None

(* The integer kind a type is, if it is one. *)
let integer_kind st ty =
  match (Memory_layout.of_type st.context.env ty).form with
  | Scalar (Integer kind) -> Some kind
  | _ -> None

let truth value = Some (Lowered.Static_scalar (Bool value))

(* An arithmetic or bitwise operation on two folded numbers, where the
   result equals the result of running the operation. Anything else, such
   as a sum that does not fit its type, is left to be run. *)
let arithmetic st ty (operation : Intrinsic.operation) (left : Lowered.static_value)
    (right : Lowered.static_value) =
  match (left, right) with
  | Static_scalar (Integer (kind, x)), Static_scalar (Integer (_, y)) -> (
      let bits = 8 * Memory_layout.integer_size (Memory_layout.target st.context.env) kind in
      let number value =
        let* kind = integer_kind st ty in
        integer st kind value
      in
      let shift by =
        if Z.sign y >= 0 && Z.lt y (Z.of_int bits) then number (by x (Z.to_int y)) else None
      in
      match operation with
      | Add -> number (Z.add x y)
      | Subtract -> number (Z.sub x y)
      | Multiply -> number (Z.mul x y)
      | Divide -> if Z.equal y Z.zero then None else number (Z.div x y)
      | Remainder -> if Z.equal y Z.zero then None else number (Z.rem x y)
      | Bit_and -> number (Z.logand x y)
      | Bit_or -> number (Z.logor x y)
      | Bit_xor -> number (Z.logxor x y)
      | Shift_left -> shift Z.shift_left
      | Shift_right -> shift Z.shift_right
      | _ -> None)
  | Static_scalar (Float64 x), Static_scalar (Float64 y) -> (
      let number value = Some (Lowered.Static_scalar (Float64 (Int64.bits_of_float value))) in
      let x = Int64.float_of_bits x and y = Int64.float_of_bits y in
      match operation with
      | Add -> number (x +. y)
      | Subtract -> number (x -. y)
      | Multiply -> number (x *. y)
      | Divide -> number (x /. y)
      | _ -> None)
  | Static_scalar (Float32 x), Static_scalar (Float32 y) -> (
      let number value = Some (Lowered.Static_scalar (Float32 (Int32.bits_of_float value))) in
      let x = Int32.float_of_bits x and y = Int32.float_of_bits y in
      match operation with
      | Add -> number (x +. y)
      | Subtract -> number (x -. y)
      | Multiply -> number (x *. y)
      | Divide -> number (x /. y)
      | _ -> None)
  | _ -> None

let negated st (value : Lowered.static_value) =
  match value with
  | Static_scalar (Integer (kind, x)) -> integer st kind (Z.neg x)
  | Static_scalar (Float64 x) ->
      Some
        (Lowered.Static_scalar (Float64 (Int64.bits_of_float (Float.neg (Int64.float_of_bits x)))))
  | Static_scalar (Float32 x) ->
      Some
        (Lowered.Static_scalar (Float32 (Int32.bits_of_float (Float.neg (Int32.float_of_bits x)))))
  | _ -> None

(* A comparison of two folded integers or two folded [Bool]s. *)
let compared (comparison : Core.comparison) (left : Lowered.static_value)
    (right : Lowered.static_value) =
  match (left, right) with
  | Static_scalar (Integer (_, x)), Static_scalar (Integer (_, y)) ->
      truth
        (match comparison with
        | Equal -> Z.equal x y
        | Not_equal -> not (Z.equal x y)
        | Less -> Z.lt x y
        | Less_equal -> Z.leq x y
        | Greater -> Z.gt x y
        | Greater_equal -> Z.geq x y)
  | Static_scalar (Bool x), Static_scalar (Bool y) -> (
      match comparison with
      | Equal -> truth (x = y)
      | Not_equal -> truth (x <> y)
      | Less | Less_equal | Greater | Greater_equal -> None)
  | _ -> None

(* How deep folding follows calls, and how many blocks it runs in all. A
   constant that needs more is left to be run. *)
let call_depth = 8
let step_limit = 10_000

let rec part (value : Lowered.static_value) (projections : Mir.projection list) =
  match (projections, value) with
  | [], _ -> Some value
  | Field name :: rest, Static_record fields ->
      let* field = List.assoc_opt name fields in
      part field rest
  | Variant_field { variant; field } :: rest, Static_variant (built, fields) when built = variant ->
      let* field = List.assoc_opt field fields in
      part field rest
  | _ -> None

(* A literal of the MIR, as static data of its type. *)
let literal st ty (constant : Mir.constant) =
  let number literal =
    match constant_of st ty literal with
    | Constant scalar -> Some (Lowered.Static_scalar scalar)
    | _ -> None
  in
  match constant with
  | Integer integer -> number (Integer_value integer)
  | Float float -> number (Float_value float)
  | Boolean boolean -> truth boolean
  | String text -> (
      match Monomorphic.shape st.context.monomorphic ty with
      | Record [ (field, Typed _) ] ->
          let bytes =
            List.init (String.length text) (fun index ->
                Lowered.Static_scalar (Integer (UInt8, Z.of_int (Char.code text.[index]))))
          in
          Some
            (Lowered.Static_record
               [
                 ( field,
                   Static_storage
                     { element = Monomorphic.builtin UInt8; elements = bytes; owned = false } );
               ])
      | _ -> None)
  | Unit -> None

let rec fold_body ~depth ~steps st (mir : Mir.t) (arguments : Lowered.static_value list) =
  let body = mir.body in
  let locals = Hashtbl.create 16 in
  let* () =
    if List.length arguments = List.length body.parameters then begin
      List.iter2 (Hashtbl.replace locals) body.parameters arguments;
      Some ()
    end
    else None
  in
  let type_of local = ground st body.locals.(local).type_ in
  let read (place : Mir.place) =
    let* whole =
      match place.root with
      | Local local -> Hashtbl.find_opt locals local
      | Constant path -> st.context.constant path
    in
    part whole place.projections
  in
  let operand : Mir.operand -> Lowered.static_value option = function
    | Use { place; _ } | Borrow { place; _ } | Take { place; _ } -> read place
    | Constant { value; type_ } -> literal st (ground st type_) value
  in
  let rvalue target : Mir.rvalue -> Lowered.static_value option = function
    | Operand value | Copy value -> operand value
    | Operation { operation = Negate; operands = [ inner ]; _ } ->
        let* inner = operand inner in
        negated st inner
    | Operation { operation; operands = [ left; right ]; _ } ->
        let* left = operand left in
        let* right = operand right in
        arithmetic st (type_of target) operation left right
    | Compare { comparison; left; right } ->
        let* left = operand left in
        let* right = operand right in
        compared comparison left right
    | Not inner -> (
        let* inner = operand inner in
        match inner with Static_scalar (Bool x) -> truth (not x) | _ -> None)
    | Construct { variant; fields } -> (
        let* fields =
          all
            (List.map
               (fun (name, field) ->
                 let* field = field in
                 let* value = operand field in
                 Some (name, value))
               fields)
        in
        match variant with
        | Some variant -> Some (Lowered.Static_variant (variant, fields))
        | None -> Some (Static_record fields))
    | Array elements ->
        let* elements = all (List.map operand elements) in
        Some (Lowered.Static_array elements)
    | Operation _ | Is_variant _ | Convert _ | To_any _ | Function_value _ | Lambda _
    | Value_parameter _ ->
        None
  in
  let assign (destination : Mir.place option) value =
    match destination with
    | Some { root = Local local; projections = [] } ->
        Hashtbl.replace locals local value;
        Some ()
    | Some _ -> None
    | None -> Some ()
  in
  let call (destination : Mir.place option) (called : Mir.call) =
    match (called.callee, called.arguments) with
    | Intrinsic { operation = Storage_with_capacity; type_arguments = [ Type element ] }, _ ->
        assign destination
          (Lowered.Static_storage { element = ground st element; elements = []; owned = true })
    | ( Intrinsic { operation = Storage_push; _ },
        [
          Passed { value = Borrow { place = { root = Local storage; projections = [] }; _ }; _ };
          Passed { value = element; _ };
        ] ) -> (
        let* element = operand element in
        match Hashtbl.find_opt locals storage with
        | Some (Static_storage contents) ->
            Hashtbl.replace locals storage
              (Static_storage { contents with elements = contents.elements @ [ element ] });
            Some ()
        | _ -> None)
    | Function { path; type_arguments }, arguments when depth > 0 ->
        let* callee_mir = demand st.context Mir.of_path path in
        let type_arguments =
          List.map
            (Monomorphic.ground_argument st.context.monomorphic st.frame.code.substitution)
            type_arguments
        in
        let callee =
          enter st.context ~builder:st.builder
            (frame_of (code_of st.context path type_arguments) ~inlined:[])
        in
        let defaults = Mir_form.parameter_defaults st.context path in
        let* values =
          all
            (List.mapi
               (fun position (argument : Mir.argument) ->
                 match argument with
                 | Passed { value; _ } -> operand value
                 | Default ->
                     let* default = List.assoc_opt position defaults in
                     fold_body ~depth:(depth - 1) ~steps callee default [])
               arguments)
        in
        let* value = fold_body ~depth:(depth - 1) ~steps callee callee_mir values in
        assign destination value
    | _ -> None
  in
  let statement (statement : Mir.statement) =
    match statement.kind with
    | Assign { target = { root = Local local; projections = [] } as target; value; _ } ->
        let* value = rvalue local value in
        assign (Some target) value
    | Call { destination; call = called } -> call destination called
    | Assert { condition; _ } -> (
        match operand condition with Some (Static_scalar (Bool true)) -> Some () | _ -> None)
    | Live _ | Dead _ | Loan_start _ | Loan_end _ | Matched _ | Ghost_assert _ | Proof _ -> Some ()
    | Assign _ | Lend _ | Slice _ | Template _ | Echo _ | Provide _ | Provide_end -> None
  in
  let rec run block =
    if !steps <= 0 then None
    else begin
      decr steps;
      let basic = body.blocks.(block) in
      let* _ = all (List.map statement basic.statements) in
      match basic.terminator with
      | Goto target -> run target
      | Branch { condition; yes; no; _ } -> (
          match operand condition with
          | Some (Static_scalar (Bool true)) -> run yes
          | Some (Static_scalar (Bool false)) -> run no
          | _ -> None)
      | Switch_variant { place; cases } -> (
          match read place with
          | Some (Static_variant (variant, _)) ->
              let* target = List.assoc_opt variant cases in
              run target
          | _ -> None)
      | Return (Some value) -> operand value
      | Return None
      | For _ | Fork _ | Join _ | Iteration_end _ | Yield _ | Cancel _ | Resume _ | Unreachable
      | Written_unreachable | Todo ->
          None
    end
  in
  run 0

(* The state to lower a constant's expression in, its MIR, and its type. *)
let constant_state context path =
  let key = key_of context path in
  let mir =
    match demand context Mir.of_constant path with
    | Some mir -> mir
    | None -> bug "%s is not a constant" (Path.show path)
  in
  let ty =
    match demand context Environment.constant_type path with
    | Some ty -> Monomorphic.ground context.monomorphic [] ty
    | None -> bug "%s has no type" (Path.show path)
  in
  let code =
    {
      (unwritten ~definition_key:key ~anchor:path ~substitution:[] ~result:(Returns Types.unit)) with
      text = text_of context key;
    }
  in
  let st =
    enter context ~builder:(create context.env ~key:(Evaluator path)) (frame_of code ~inlined:[])
  in
  (st, mir, ty)

(* A constant's static data, where its value folds, and otherwise the type
   of the value its evaluator computes. *)
type constant = Folded of Lowered.data | Run of Ground.ty

let constant context path =
  let st, mir, ty = constant_state context path in
  match fold_body ~depth:call_depth ~steps:(ref step_limit) st mir [] with
  | Some value -> Folded { data_key = Constant path; ty; value }
  | None -> Run ty

(* Code run while compiling appends its results, in their binary form,
   to an output it owns, and writes that to standard output as it ends, with
   the standard library's function that writes every byte. *)
let begin_output st =
  let output = temporary st Glue.output_ty in
  emit st.builder (Assign (output, Storage.empty Glue.output_ty));
  output

let write_fully = Well_known.path Write_fully

let write_output st output =
  let builder = st.builder in
  let int32 = Monomorphic.builtin Int32 in
  let view_ty = Storage.view_of_elements (Monomorphic.builtin UInt8) in
  let descriptor = temporary st int32 and view = temporary st view_ty in
  emit builder (Assign (descriptor, Use (Constant (Integer (Int32, Z.one)))));
  emit builder
    (Assign
       ( view,
         Storage.view view_ty
           ~elements:(Copy (Storage.buffer output))
           ~length:(Copy (Storage.length output)) ));
  let signature = signature_of st.context write_fully in
  let result =
    match signature.output with
    | Returns ty -> Monomorphic.ground st.context.monomorphic [] ty
    | Lends _ -> bug "write_fully does not return"
  in
  call_instance st
    (Code { path = write_fully; type_arguments = [] })
    ~signature ~substitution:[]
    ~arguments:[ (Read, int32, descriptor); (Read, view_ty, view) ]
    ~destination:(temporary st result) ()

(* Code run while compiling: computes a constant's value and writes its
   binary form to standard output. *)
let evaluator context path : Emit_c.Builder.instance =
  let st, mir, ty = constant_state context path in
  start st.builder (block st.builder);
  in_scope st (fun () ->
      let place = temporary st ty in
      Mir_form.mir_into st mir place;
      let output = begin_output st in
      Glue.encode_call context.glue st.builder
        ~output:(Address { place = output; writable = true })
        ty place;
      write_output st output);
  finish_instance st ~rest:[] ()
