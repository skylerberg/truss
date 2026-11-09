(* The LIR's canonical encoding, in deterministic CBOR, and its hash. See lir.mli. *)

open Ir

let version = 10
let tagged n items = Cbor.Array (Cbor.int n :: items)
let list f items = Cbor.Array (List.map f items)
let option f = function None -> Cbor.Null | Some x -> f x

let integer_tag = function
  | Memory_layout.Int8 -> 0
  | Int16 -> 1
  | Int32 -> 2
  | Int64 -> 3
  | UInt8 -> 4
  | UInt16 -> 5
  | UInt32 -> 6
  | UInt64 -> 7
  | USize -> 8
  | ISize -> 9

(* How references to other definitions are written: every path, and every
   instance. *)
type encoders = { path : Path.t -> Cbor.t; instance : Instance.key -> Cbor.t }

let rec encode_scalar instance (scalar : Memory_layout.scalar) =
  match scalar with
  | Integer integer -> tagged 0 [ Cbor.int (integer_tag integer) ]
  | Float32 -> tagged 1 []
  | Float64 -> tagged 2 []
  | Bool -> tagged 3 []
  | Character -> tagged 4 []
  | Pointer pointee -> tagged 5 [ encode_pointee instance pointee ]
  | Nullable_pointer pointee -> tagged 6 [ encode_pointee instance pointee ]

and encode_pointee e : Memory_layout.pointee -> Cbor.t = function
  | Data ty -> tagged 0 [ Ground.encode ~path:e.path ty ]
  | Block (ty, variant) -> tagged 1 [ Ground.encode ~path:e.path ty; Text variant ]
  | Code f -> tagged 2 [ Ground.encode ~path:e.path (Function f) ]
  | Opaque -> tagged 3 []

let rec encode_ty instance = function
  | Value ty -> tagged 0 [ Ground.encode ~path:instance.path ty ]
  | Pointer { target; writable } -> tagged 1 [ encode_ty instance target; Bool writable ]
  | Raw scalar -> tagged 2 [ encode_scalar instance scalar ]
  | Environment n -> tagged 3 [ Cbor.int n ]
  | Evidence n -> tagged 4 [ Cbor.int n ]

let encode_function_ref instance = function
  | Instance key -> tagged 0 [ instance.instance key ]
  | Nested n -> tagged 1 [ Cbor.int n ]

let rec encode_place instance (place : place) =
  Cbor.Array
    [
      (match place.root with
      | Local local -> tagged 0 [ Cbor.int local ]
      | Static { key; ty } ->
          tagged 1 [ instance.instance key; Ground.encode ~path:instance.path ty ]);
      list (encode_projection instance) place.projections;
    ]

and encode_projection instance = function
  | Field name -> tagged 0 [ Text name ]
  | Variant_field { variant; field } -> tagged 1 [ Text variant; Text field ]
  | Index operand -> tagged 2 [ encode_operand instance operand ]
  | Deref -> tagged 3 []

and encode_operand instance = function
  | Copy place -> tagged 0 [ encode_place instance place ]
  | Move place -> tagged 1 [ encode_place instance place ]
  | Constant constant -> tagged 2 [ encode_constant instance constant ]
  | Address { place; writable } -> tagged 3 [ encode_place instance place; Bool writable ]
  | Moved_address place -> tagged 4 [ encode_place instance place ]

and encode_constant instance = function
  | Integer (integer, value) -> tagged 0 [ Cbor.int (integer_tag integer); Integer value ]
  | Float32 bits -> tagged 1 [ Integer (Z.of_int32_unsigned bits) ]
  | Float64 bits -> tagged 2 [ Integer (Z.of_int64_unsigned bits) ]
  | Bool value -> tagged 3 [ Bool value ]
  | Character code -> tagged 4 [ Cbor.int code ]
  | Bytes text -> tagged 5 [ Bytes text ]
  | Null -> tagged 6 []
  | Symbol_address key -> tagged 7 [ instance.instance key ]
  | Size_of ty -> tagged 8 [ Ground.encode ~path:instance.path ty ]
  | Alignment_of ty -> tagged 9 [ Ground.encode ~path:instance.path ty ]

let encode_signature instance (s : signature) =
  Cbor.Array
    [ list (encode_ty instance) s.parameters; option (encode_ty instance) s.result; Bool s.returns ]

let unary_tag = function Negate -> 0 | Not -> 1 | Complement -> 2

let binary_tag = function
  | Add -> 0
  | Subtract -> 1
  | Multiply -> 2
  | Divide -> 3
  | Remainder -> 4
  | Bit_and -> 5
  | Bit_or -> 6
  | Bit_xor -> 7
  | Shift_left -> 8
  | Shift_right -> 9
  | Equal -> 10
  | Not_equal -> 11
  | Less -> 12
  | Less_equal -> 13
  | Greater -> 14
  | Greater_equal -> 15
  | Ieee_equal -> 16
  | Ieee_less -> 17
  | Ieee_less_equal -> 18

let intrinsic_tag = function
  | Allocate -> 0
  | Reallocate -> 1
  | Free -> 2
  | Copy_bytes -> 3
  | Move_bytes -> 4
  | Compare_bytes -> 5
  | Add_overflow -> 6
  | Subtract_overflow -> 7
  | Multiply_overflow -> 8
  | Leading_zeros -> 9
  | Trailing_zeros -> 10
  | Count_ones -> 11
  | Swap_bytes -> 12
  | Rotate_left -> 13
  | Rotate_right -> 14
  | Multiply_high -> 15
  | Square_root -> 16
  | Fused_multiply_add -> 17
  | Floor -> 18
  | Ceiling -> 19
  | Truncate -> 20
  | Round_even -> 21
  | Float_bits -> 22
  | Float_from_bits -> 23
  | Grow -> 24
  | System_write -> 25
  | System_read -> 26
  | Clock_now -> 27
  | Random_fill -> 28
  | Debug_begin -> 29
  | Debug_text -> 30
  | Debug_signed -> 31
  | Debug_unsigned -> 32
  | Debug_float32 -> 33
  | Debug_float64 -> 34
  | Debug_bool -> 35
  | Debug_character -> 36
  | Debug_string -> 37
  | Debug_bytes -> 38
  | Debug_length -> 39
  | Evidence_implementation -> 40
  | Evidence_outer -> 41
  | Program_argument -> 42
  | Float_text -> 43
  | Evidence_fill -> 44
  | System_environment -> 45
  | System_open -> 46
  | System_close -> 47
  | System_run -> 48

let encode_rvalue instance rvalue =
  let operand = encode_operand instance in
  match rvalue with
  | Use o -> tagged 0 [ operand o ]
  | Unary (op, o) -> tagged 1 [ Cbor.int (unary_tag op); operand o ]
  | Binary (op, a, b) -> tagged 2 [ Cbor.int (binary_tag op); operand a; operand b ]
  | Convert (o, scalar) -> tagged 3 [ operand o; encode_scalar instance scalar ]
  | Build { ty; variant; fields } ->
      tagged 4
        [
          Ground.encode ~path:instance.path ty;
          option (fun v -> Cbor.Text v) variant;
          list (fun (name, o) -> Cbor.Array [ Text name; operand o ]) fields;
        ]
  | Is_variant (place, variant) -> tagged 5 [ encode_place instance place; Text variant ]
  | Function_value { code; environment } ->
      tagged 6 [ encode_function_ref instance code; option operand environment ]

let encode_target instance = function
  | Direct { function_; signature } ->
      tagged 0 [ encode_function_ref instance function_; encode_signature instance signature ]
  | Indirect { value; signature } ->
      tagged 1 [ encode_operand instance value; encode_signature instance signature ]
  | Intrinsic intrinsic -> tagged 2 [ Cbor.int (intrinsic_tag intrinsic) ]
  | Evidence_call { evidence; slot; signature } ->
      tagged 3
        [ encode_operand instance evidence; Cbor.int slot; encode_signature instance signature ]
  | Table_call { table; value; slot; signature } ->
      tagged 4
        [
          encode_operand instance table;
          encode_operand instance value;
          Cbor.int slot;
          encode_signature instance signature;
        ]

let encode_statement instance = function
  | Assign (place, rvalue) ->
      tagged 0 [ encode_place instance place; encode_rvalue instance rvalue ]
  | Call { target; arguments; result } ->
      tagged 1
        [
          encode_target instance target;
          list (encode_operand instance) arguments;
          (match result with
          | Discarded -> tagged 0 []
          | Returned place -> tagged 1 [ encode_place instance place ]
          | Written place -> tagged 2 [ encode_place instance place ]);
        ]
  | Drop place -> tagged 2 [ encode_place instance place ]
  | Free_block { place; variant } -> tagged 3 [ encode_place instance place; Text variant ]
  | Echo { text; length; site } ->
      tagged 4
        [
          encode_operand instance text;
          encode_operand instance length;
          instance.path site.definition;
          Cbor.int site.line;
          Cbor.int site.column;
        ]

let encode_terminator instance terminator =
  let operand = encode_operand instance in
  let cases f cases = list (fun (value, block) -> Cbor.Array [ f value; Cbor.int block ]) cases in
  let block = option Cbor.int in
  match terminator with
  | Goto b -> tagged 0 [ Cbor.int b ]
  | Switch { value; cases = c; default } ->
      tagged 1 [ operand value; cases (fun v -> Cbor.Integer v) c; block default ]
  | Switch_variant { place; cases = c; default } ->
      tagged 2 [ encode_place instance place; cases (fun v -> Cbor.Text v) c; block default ]
  | Return value -> tagged 3 [ option operand value ]
  | Unreachable -> tagged 4 []
  | Fail { failure; message; length; site } ->
      tagged 5
        [
          Cbor.int (match failure with Panic -> 0 | Assertion -> 1 | Todo -> 2);
          operand message;
          operand length;
          instance.path site.definition;
          Cbor.int site.line;
          Cbor.int site.column;
        ]
  | Yield { value; resume; stop } -> tagged 6 [ operand value; Cbor.int resume; block stop ]

let encode_function instance (f : function_) =
  Cbor.Array
    [
      list Cbor.int f.parameters;
      option Cbor.int f.written_result;
      option (encode_ty instance) f.result;
      Bool f.returns;
      list
        (fun (local : local_info) ->
          Cbor.Array [ encode_ty instance local.ty; option (fun n -> Cbor.Text n) local.name ])
        (Array.to_list f.locals);
      list
        (fun (b : basic_block) ->
          Cbor.Array
            [
              list (encode_statement instance) b.statements; encode_terminator instance b.terminator;
            ])
        (Array.to_list f.blocks);
      list (fun (name, ty) -> Cbor.Array [ Text name; encode_ty instance ty ]) f.environment;
    ]

let encode ?(path = Ground.encode_path) ?instance t =
  let instance = match instance with Some instance -> instance | None -> Instance.encode ~path in
  let encoders = { path; instance } in
  Cbor.Array
    [
      instance t.key;
      encode_function encoders t.main;
      list (encode_function encoders) (Array.to_list t.nested);
    ]

let rec encode_static (e : encoders) = function
  | Static_scalar constant -> tagged 0 [ encode_constant e constant ]
  | Static_record fields ->
      tagged 1 [ list (fun (name, v) -> Cbor.Array [ Text name; encode_static e v ]) fields ]
  | Static_variant (variant, fields) ->
      tagged 2
        [ Text variant; list (fun (name, v) -> Cbor.Array [ Text name; encode_static e v ]) fields ]
  | Static_array values -> tagged 3 [ list (encode_static e) values ]
  | Static_storage { element; elements; owned } ->
      tagged 4 [ Ground.encode ~path:e.path element; list (encode_static e) elements; Bool owned ]

let encode_data ?(path = Ground.encode_path) ?instance data =
  let instance = match instance with Some instance -> instance | None -> Instance.encode ~path in
  Cbor.Array
    [
      instance data.data_key;
      Ground.encode ~path data.ty;
      encode_static { path; instance } data.value;
    ]

let encode_table ?(path = Ground.encode_path) ?instance (table : table) =
  let instance = match instance with Some instance -> instance | None -> Instance.encode ~path in
  let encoders_default = { path; instance } in
  Cbor.Array
    [
      instance table.table_key;
      list
        (fun (key, s) -> Cbor.Array [ instance key; encode_signature encoders_default s ])
        table.entries;
    ]

let encode_evidence ?(path = Ground.encode_path) ?instance (evidence : evidence) =
  let instance = match instance with Some instance -> instance | None -> Instance.encode ~path in
  Cbor.Array
    [ instance evidence.evidence_key; instance evidence.table; list instance evidence.outer ]

let hash t =
  Blake3.hash
    (Cbor.encode (Cbor.Array [ Text "truss lir"; Cbor.int version; encode (canonical_instance t) ]))
