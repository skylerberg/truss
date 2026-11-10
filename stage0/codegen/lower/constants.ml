(* Constants: a constant's value folded exactly from its expression, or
   worked out by running its evaluator. *)

open Definitions
open Lowering
open Targets
open Matching
open Expressions
open Lir_builder

(* Constants *)

let ( let* ) = Option.bind

(* Every value, if each of them is there. *)
let all values =
  List.fold_right
    (fun value rest ->
      let* value = value in
      let* rest = rest in
      Some (value :: rest))
    values (Some [])

(* An integer of a kind, if the kind holds it. *)
let integer st (kind : Memory_layout.integer) value =
  let bits = 8 * Memory_layout.integer_size (Memory_layout.target st.context.env) kind in
  let low, high =
    match kind with
    | Int8 | Int16 | Int32 | Int64 | ISize ->
        (Z.neg (Z.shift_left Z.one (bits - 1)), Z.pred (Z.shift_left Z.one (bits - 1)))
    | UInt8 | UInt16 | UInt32 | UInt64 | USize -> (Z.zero, Z.pred (Z.shift_left Z.one bits))
  in
  if Z.leq low value && Z.leq value high then Some (Lir.Static_scalar (Integer (kind, value)))
  else None

(* The integer kind a type is, if it is one. *)
let integer_kind st ty =
  match (Memory_layout.of_type st.context.env ty).form with
  | Scalar (Integer kind) -> Some kind
  | _ -> None

let truth value = Some (Lir.Static_scalar (Bool value))

(* An operator on two folded values, where both are numbers or both [Bool]
   and the result is exactly what running the operator gives. Anything else,
   such as a sum that does not fit its type, is left to be run. *)
let binary st ty (operator : S.binary) (left : Lir.static_value) (right : Lir.static_value) =
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
      match operator with
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
      | Equal -> truth (Z.equal x y)
      | Not_equal -> truth (not (Z.equal x y))
      | Less -> truth (Z.lt x y)
      | Less_equal -> truth (Z.leq x y)
      | Greater -> truth (Z.gt x y)
      | Greater_equal -> truth (Z.geq x y)
      | And | Or | Implies -> None)
  | Static_scalar (Float64 x), Static_scalar (Float64 y) -> (
      let number value = Some (Lir.Static_scalar (Float64 (Int64.bits_of_float value))) in
      let x = Int64.float_of_bits x and y = Int64.float_of_bits y in
      match operator with
      | Add -> number (x +. y)
      | Subtract -> number (x -. y)
      | Multiply -> number (x *. y)
      | Divide -> number (x /. y)
      | _ -> None)
  | Static_scalar (Float32 x), Static_scalar (Float32 y) -> (
      let number value = Some (Lir.Static_scalar (Float32 (Int32.bits_of_float value))) in
      let x = Int32.float_of_bits x and y = Int32.float_of_bits y in
      match operator with
      | Add -> number (x +. y)
      | Subtract -> number (x -. y)
      | Multiply -> number (x *. y)
      | Divide -> number (x /. y)
      | _ -> None)
  | Static_scalar (Bool x), Static_scalar (Bool y) -> (
      match operator with
      | And -> truth (x && y)
      | Or -> truth (x || y)
      | Equal -> truth (x = y)
      | Not_equal -> truth (x <> y)
      | _ -> None)
  | _ -> None

(* A constant expression's value, where it can be worked out here exactly
   as running it would: literals, operators on numbers and on [Bool],
   other constants that fold, and records, variants, strings, lists, and
   arrays built from parts that fold. For anything else there is none, and
   the value is worked out by running the constant's evaluator. Running is
   what a constant's value means; folding only saves the run. *)
let rec fold st (e : S.expression) : Lir.static_value option =
  let ty = type_of st e.id in
  let checked = st.frame.code.checked in
  let number value =
    match constant_of st ty value with Constant c -> Some (Lir.Static_scalar c) | _ -> None
  in
  match e.kind with
  | Parenthesized inner -> fold st inner
  | Integer _ | Float _ -> number (literal st e.id)
  | Prefix (Negate, ({ kind = Integer _; _ } as inner)) when checked.calls.(e.id) = None -> (
      match literal st inner.id with
      | Integer_value v -> number (Integer_value (Z.neg v))
      | Float_value v -> number (Float_value (Float.neg v)))
  | True -> truth true
  | False -> truth false
  | String _ when checked.literals.(e.id) <> None -> number (literal st e.id)
  | String literal when literal.rest = [] && literal.tag = None -> (
      match Monomorphic.shape st.context.monomorphic ty with
      | Record [ (field, Typed _) ] ->
          let bytes =
            List.init (String.length literal.first.value) (fun i ->
                Lir.Static_scalar (Integer (UInt8, Z.of_int (Char.code literal.first.value.[i]))))
          in
          Some
            (Lir.Static_record
               [
                 ( field,
                   Static_storage
                     { element = Monomorphic.builtin UInt8; elements = bytes; owned = false } );
               ])
      | _ -> None)
  | List elements -> (
      let* values = all (List.map (fold st) elements) in
      match Monomorphic.shape st.context.monomorphic ty with
      | Array _ -> Some (Lir.Static_array values)
      | Record [ (field, Typed storage) ] -> (
          match Monomorphic.kind st.context.monomorphic storage with
          | Storage element ->
              Some
                (Lir.Static_record
                   [ (field, Static_storage { element; elements = values; owned = true }) ])
          | _ -> None)
      | _ -> None)
  | Name _ | Member _ -> (
      match checked.meanings.(e.id) with
      | Some (Global { path; _ }) -> !(st.context.constant) path
      | Some (Variant_value { variant; _ }) -> Some (Lir.Static_variant (variant, []))
      | _ -> None)
  | Call (_, arguments) -> (
      match checked.calls.(e.id) with
      | Some { callee = Constructor { variant; _ }; arguments = passed; defaults_left_out = []; _ }
        ->
          let names = constructor_fields st ty variant in
          let* fields =
            all
              (List.map
                 (fun (argument : C.argument) ->
                   let* written =
                     List.find_opt
                       (fun (a : S.argument) -> a.value.id = argument.expression)
                       arguments
                   in
                   let* value = fold st written.value in
                   let* name = List.nth_opt names argument.parameter in
                   Some (name, value))
                 passed)
          in
          Some
            (match variant with
            | Some v -> Lir.Static_variant (v, fields)
            | None -> Static_record fields)
      | _ -> None)
  | Binary { operator; left; right; _ } ->
      let* left = fold st left in
      let* right = fold st right in
      binary st ty operator left right
  | Prefix (Negate, inner) -> (
      let* value = fold st inner in
      match value with
      | Static_scalar (Integer (kind, x)) -> integer st kind (Z.neg x)
      | Static_scalar (Float64 x) ->
          Some
            (Lir.Static_scalar (Float64 (Int64.bits_of_float (Float.neg (Int64.float_of_bits x)))))
      | Static_scalar (Float32 x) ->
          Some
            (Lir.Static_scalar (Float32 (Int32.bits_of_float (Float.neg (Int32.float_of_bits x)))))
      | _ -> None)
  | Prefix (Not, inner) -> (
      let* value = fold st inner in
      match value with Static_scalar (Bool x) -> truth (not x) | _ -> None)
  | _ -> None

(* The state to lower a constant's expression in, the expression, and its
   type. *)
let constant_state context path =
  let key = key_of context path in
  let value =
    match demand context Names.definition key with
    | Some { kind = Constant { value; _ }; _ } -> value
    | _ -> bug "%s is not a constant" (Path.show path)
  in
  let ty =
    match demand context Environment.constant_type path with
    | Some ty -> Monomorphic.ground context.monomorphic [] ty
    | None -> bug "%s has no type" (Path.show path)
  in
  let code =
    {
      (unwritten ~definition_key:key ~anchor:path ~substitution:[] ~result:(Returns T.unit)) with
      text = text_of context key;
      checked = checked_of context key;
    }
  in
  let st = enter context (frame_of code ~inlined:[]) in
  (st, value, ty)

(* A constant's static data, where its value folds, and otherwise the type
   of the value its evaluator works out. *)
type constant = Folded of Lir.data | Run of Ground.ty

let constant context path =
  let st, value, ty = constant_state context path in
  match fold st value with
  | Some value -> Folded { data_key = Constant path; ty; value }
  | None -> Run ty

(* Code run while compiling leaves what it works out in the debug buffer, in
   its binary form, and writes the buffer to standard output as it ends,
   with the standard library's function that writes every byte. *)
let begin_output st =
  emit st.b (Call { target = Intrinsic Debug_begin; arguments = []; result = Discarded })

let write_fully : Path.t =
  Top { module_ = { package = "standard"; modules = [ "system"; "calls" ] }; name = "write_fully" }

let write_output st =
  let b = st.b in
  let call intrinsic result =
    emit b (Call { target = Intrinsic intrinsic; arguments = []; result = Returned result })
  in
  let bytes = local b (Raw (Pointer Opaque)) and length = temporary st st.context.types.usize in
  call Debug_bytes (at bytes);
  call Debug_length length;
  let int32 = Monomorphic.builtin Int32 in
  let view_ty = Storage.view_of_elements (Monomorphic.builtin UInt8) in
  let output = temporary st int32 and view = temporary st view_ty in
  emit b (Assign (output, Use (Constant (Integer (Int32, Z.one)))));
  emit b (Assign (view, Storage.view view_ty ~elements:(Copy (at bytes)) ~length:(Copy length)));
  let signature = signature_of st.context write_fully in
  let result =
    match signature.output with
    | Returns ty -> Monomorphic.ground st.context.monomorphic [] ty
    | Yields _ | Lends _ -> bug "write_fully does not return"
  in
  call_instance st
    (Code { path = write_fully; type_arguments = [] })
    ~signature ~substitution:[]
    ~arguments:[ (Read, int32, output); (Read, view_ty, view) ]
    ~mask:0 ~destination:(temporary st result)

(* Code run while compiling: works out a constant's value and writes its
   binary form to standard output. *)
let evaluator context path : Lir.t =
  let st, value, ty = constant_state context path in
  start st.b (block st.b);
  in_scope st (fun () ->
      let place = temporary st ty in
      into st value place;
      begin_output st;
      Glue.encode_call context.glue st.b ty place;
      write_output st);
  {
    key = Evaluator path;
    main = finish_function st ~first:[] ~rest:[] ();
    nested = nested_functions st;
  }
