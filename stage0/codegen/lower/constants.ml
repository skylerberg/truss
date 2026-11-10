(* Constants: a constant's value folded exactly from its expression, or
   worked out by running its evaluator. *)

open Definitions
open Lowering
open Targets
open Matching
open Expressions
open Lir_builder

(* Constants *)

(* Wraps an integer to a type's width, as a shift may need. *)
let wrap st ty value =
  let integer = integer_of st ty in
  let bytes = Memory_layout.integer_size (Memory_layout.target st.context.env) integer in
  let bits = 8 * bytes in
  let modulus = Z.shift_left Z.one bits in
  let low = Z.erem value modulus in
  match integer with
  | Int8 | Int16 | Int32 | Int64 | ISize ->
      if Z.geq low (Z.shift_left Z.one (bits - 1)) then Z.sub low modulus else low
  | _ -> low

(* A constant expression's value, worked out exactly: literals, arithmetic
   on numbers, other constants, and records, variants, strings, lists, and
   arrays built from constant parts. *)
let rec static_of st (e : S.expression) : Lir.static_value =
  let ty = type_of st e.id in
  let number value : Lir.static_value =
    Static_scalar (match operand_constant st ty value with c -> c)
  in
  match e.kind with
  | Parenthesized inner -> static_of st inner
  | Integer _ | Float _ -> number (literal st e.id)
  | Prefix (Negate, ({ kind = Integer _; _ } as inner))
    when st.frame.code.checked.calls.(e.id) = None -> (
      match literal st inner.id with
      | Integer_value v -> number (Integer_value (Z.neg v))
      | Float_value v -> number (Float_value (Float.neg v)))
  | True -> Static_scalar (Bool true)
  | False -> Static_scalar (Bool false)
  | String _ when st.frame.code.checked.literals.(e.id) <> None -> number (literal st e.id)
  | String literal when literal.rest = [] && literal.tag = None -> (
      match Monomorphic.shape st.context.monomorphic ty with
      | Record [ (field, Typed _) ] ->
          let bytes =
            List.init (String.length literal.first.value) (fun i ->
                Lir.Static_scalar (Integer (UInt8, Z.of_int (Char.code literal.first.value.[i]))))
          in
          Static_record
            [
              ( field,
                Static_storage
                  { element = Monomorphic.builtin UInt8; elements = bytes; owned = false } );
            ]
      | _ -> bug "a string constant of %s" (Ground.to_string ty))
  | List elements -> (
      match Monomorphic.shape st.context.monomorphic ty with
      | Array _ -> Static_array (List.map (static_of st) elements)
      | Record [ (field, Typed storage) ] -> (
          match Monomorphic.kind st.context.monomorphic storage with
          | Storage element ->
              Static_record
                [
                  ( field,
                    Static_storage
                      { element; elements = List.map (static_of st) elements; owned = true } );
                ]
          | _ -> raise Needs_running)
      | _ -> raise Needs_running)
  | Name _ | Member _ -> (
      match st.frame.code.checked.meanings.(e.id) with
      | Some (Global { path; _ }) -> (constant_data st.context path).value
      | Some (Variant_value { variant; _ }) -> Static_variant (variant, [])
      | _ -> bug "a constant that names something else: %s" (source st e.span))
  | Call (_, arguments) -> (
      match st.frame.code.checked.calls.(e.id) with
      | Some { callee = Constructor { variant; _ }; arguments = checked; _ } -> (
          let names = constructor_fields st ty variant in
          let fields =
            List.map
              (fun (argument : C.argument) ->
                let value =
                  (List.find (fun (a : S.argument) -> a.value.id = argument.expression) arguments)
                    .value
                in
                (List.nth names argument.parameter, static_of st value))
              checked
          in
          match variant with Some v -> Static_variant (v, fields) | None -> Static_record fields)
      | _ -> raise Needs_running)
  | Binary { operator; left; right; _ } ->
      fold st ty ~operator:(Some operator) [ static_of st left; static_of st right ]
  | Prefix (Negate, inner) -> fold st ty ~operator:None [ static_of st inner ]
  | _ -> raise Needs_running

and operand_constant st ty literal =
  match constant_of st ty literal with
  | Constant c -> c
  | _ -> bug "a literal that is not a constant"

(* Arithmetic on constant numbers, exact for integers, which the type
   checker has shown do not overflow, and IEEE for floats. *)
and fold st ty ~operator values : Lir.static_value =
  let integer = function
    | Lir.Static_scalar (Integer (_, v)) -> v
    | _ -> bug "an integer constant"
  in
  let real = function
    | Lir.Static_scalar (Float64 bits) -> Int64.float_of_bits bits
    | Static_scalar (Float32 bits) -> Int32.float_of_bits bits
    | _ -> bug "a float constant"
  in
  match scalar_of st ty with
  | Integer kind -> (
      let v op = Lir.Static_scalar (Integer (kind, wrap st ty op)) in
      match (operator, List.map integer values) with
      | None, [ a ] -> v (Z.neg a)
      | Some Add, [ a; b ] -> v (Z.add a b)
      | Some Subtract, [ a; b ] -> v (Z.sub a b)
      | Some Multiply, [ a; b ] -> v (Z.mul a b)
      | Some Divide, [ a; b ] -> v (Z.div a b)
      | Some Remainder, [ a; b ] -> v (Z.rem a b)
      | Some Bit_and, [ a; b ] -> v (Z.logand a b)
      | Some Bit_or, [ a; b ] -> v (Z.logor a b)
      | Some Bit_xor, [ a; b ] -> v (Z.logxor a b)
      | Some Shift_left, [ a; b ] -> v (Z.shift_left a (Z.to_int b))
      | Some Shift_right, [ a; b ] -> v (Z.shift_right a (Z.to_int b))
      | _ -> bug "an operation in a constant that is not folded")
  | (Float32 | Float64) as scalar -> (
      let v x =
        Lir.Static_scalar
          (if scalar = Float32 then Float32 (Int32.bits_of_float x)
           else Float64 (Int64.bits_of_float x))
      in
      match (operator, List.map real values) with
      | None, [ a ] -> v (Float.neg a)
      | Some Add, [ a; b ] -> v (a +. b)
      | Some Subtract, [ a; b ] -> v (a -. b)
      | Some Multiply, [ a; b ] -> v (a *. b)
      | Some Divide, [ a; b ] -> v (a /. b)
      | _ -> bug "an operation in a constant that is not folded")
  | _ -> bug "arithmetic in a constant on %s" (Ground.to_string ty)

(* A constant's static data: folded while compiling, or else worked out by
   running its code. *)
and constant_data context path : Lir.data =
  let st, value, ty = constant_state context path in
  let value = try static_of st value with Needs_running -> !(context.evaluate) path ty in
  { data_key = Constant path; ty; value }

(* The state to lower a constant's expression in, the expression, and its
   type. *)
and constant_state context path =
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

let constant context path = constant_data context path

(* Code run while compiling leaves what it works out in the debug buffer, in
   its binary form, and writes the buffer to standard output as it ends. *)
let begin_output st =
  emit st.b (Call { target = Intrinsic Debug_begin; arguments = []; result = Discarded })

let write_output st =
  let b = st.b in
  let call intrinsic arguments result =
    emit b (Call { target = Intrinsic intrinsic; arguments; result = Returned result })
  in
  let bytes = local b (Raw (Pointer Opaque)) and length = temporary st st.context.types.usize in
  call Debug_bytes [] (at bytes);
  call Debug_length [] length;
  call System_write
    [ Constant (Integer (Int32, Z.one)); Copy (at bytes); Copy length ]
    (temporary st st.context.types.isize)

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
