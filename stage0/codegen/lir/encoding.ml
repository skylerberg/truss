(* The LIR's canonical encoding, in deterministic CBOR, and its hash. *)

open Ir

let version = 25
let tagged tag items = Cbor.Array (Cbor.int tag :: items)
let list encode_item items = Cbor.Array (List.map encode_item items)
let option encode_item = function None -> Cbor.Null | Some item -> encode_item item

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

and encode_pointee pointee_encoder : Memory_layout.pointee -> Cbor.t = function
  | Data ty -> tagged 0 [ Ground.encode ~path:pointee_encoder.path ty ]
  | Block (ty, variant) -> tagged 1 [ Ground.encode ~path:pointee_encoder.path ty; Text variant ]
  | Code encode_item -> tagged 2 [ Ground.encode ~path:pointee_encoder.path (Function encode_item) ]
  | Opaque -> tagged 3 []

let rec encode_ty instance = function
  | Value ty -> tagged 0 [ Ground.encode ~path:instance.path ty ]
  | Pointer { target; writable } -> tagged 1 [ encode_ty instance target; Bool writable ]
  | Raw scalar -> tagged 2 [ encode_scalar instance scalar ]
  | Environment tag -> tagged 3 [ Cbor.int tag ]
  | Evidence tag -> tagged 4 [ Cbor.int tag ]

let encode_function_ref instance = function
  | Instance key -> tagged 0 [ instance.instance key ]
  | Nested tag -> tagged 1 [ Cbor.int tag ]

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
  | Site site ->
      tagged 10 [ instance.path site.definition; Cbor.int site.line; Cbor.int site.column ]

let encode_signature instance (lir_signature : signature) =
  Cbor.Array
    [
      list (encode_ty instance) lir_signature.parameters;
      option (encode_ty instance) lir_signature.result;
      Bool lir_signature.returns;
    ]

let equal_signature left right =
  let encoders = { path = Ground.encode_path; instance = Instance.encode } in
  String.equal
    (Cbor.encode (encode_signature encoders left))
    (Cbor.encode (encode_signature encoders right))

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
  | Evidence_implementation -> 40
  | Evidence_outer -> 41
  | Program_argument -> 42
  | Evidence_fill -> 44
  | Environment -> 49
  | Run_test -> 51
  | Report_tests_to -> 52
  | Live_blocks -> 53
  | Terminated_length -> 50
  | Coroutine_start -> 54
  | Coroutine_resume -> 55
  | Coroutine_suspend -> 56
  | Tasks_spawn -> 57
  | Shared_allocate -> 58
  | Shared_retain -> 59
  | Shared_release -> 60
  | Shared_free -> 61
  | Shared_lock -> 62
  | Shared_unlock -> 63
  | Blocking_begin -> 64
  | Blocking_end -> 65

let encode_rvalue instance rvalue =
  let operand = encode_operand instance in
  match rvalue with
  | Use lir_operand -> tagged 0 [ operand lir_operand ]
  | Unary (op, lir_operand) -> tagged 1 [ Cbor.int (unary_tag op); operand lir_operand ]
  | Binary (op, left, right) -> tagged 2 [ Cbor.int (binary_tag op); operand left; operand right ]
  | Convert (lir_operand, scalar) -> tagged 3 [ operand lir_operand; encode_scalar instance scalar ]
  | Build { ty; variant; fields } ->
      tagged 4
        [
          Ground.encode ~path:instance.path ty;
          option (fun variant_name -> Cbor.Text variant_name) variant;
          list (fun (name, lir_operand) -> Cbor.Array [ Text name; operand lir_operand ]) fields;
        ]
  | Is_variant (place, variant) -> tagged 5 [ encode_place instance place; Text variant ]
  | Function_value { code; environment } ->
      tagged 6 [ encode_function_ref instance code; option operand environment ]

let rec encode_c_type : Libc.c_type -> Cbor.t = function
  | Void -> tagged 0 []
  | Named name -> tagged 1 [ Text name ]
  | Struct name -> tagged 2 [ Text name ]
  | Const c_type -> tagged 3 [ encode_c_type c_type ]
  | Pointer c_type -> tagged 4 [ encode_c_type c_type ]

let encode_foreign (declaration : Libc.declaration) =
  Cbor.Array
    [
      Text declaration.symbol;
      encode_c_type declaration.returns;
      Bool declaration.never_returns;
      list encode_c_type declaration.takes;
      option Cbor.int declaration.variadic_from;
    ]

let encode_target instance = function
  | Direct { function_; signature } ->
      tagged 0 [ encode_function_ref instance function_; encode_signature instance signature ]
  | Indirect { value; signature } ->
      tagged 1 [ encode_operand instance value; encode_signature instance signature ]
  | Intrinsic intrinsic -> tagged 2 [ Cbor.int (intrinsic_tag intrinsic) ]
  | Foreign declaration -> tagged 5 [ encode_foreign declaration ]
  | Evidence_call { evidence; capability; slot; signature } ->
      tagged 3
        [
          encode_operand instance evidence;
          instance.path capability;
          Cbor.int slot;
          encode_signature instance signature;
        ]
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
  | Region { fork; region = Branch } -> tagged 5 [ Cbor.int fork ]
  | Region { fork; region = Chunk { first; last } } ->
      tagged 6 [ Cbor.int fork; Cbor.int first; Cbor.int last ]
  | Region { fork; region = Task { function_value; item } } ->
      tagged 10 [ Cbor.int fork; Cbor.int function_value; Cbor.int item ]
  | Regions_end { fork } -> tagged 7 [ Cbor.int fork ]
  | Loop_body { loop; part } -> tagged 11 [ Cbor.int loop; option Cbor.int part ]
  | Loop_exit { loop } -> tagged 12 [ Cbor.int loop ]
  | Fork { branches } ->
      tagged 8
        [
          list
            (fun (nested, environment) ->
              Cbor.Array [ Cbor.int nested; encode_operand instance environment ])
            branches;
        ]
  | Fork_range { body; environment; first; last } ->
      tagged 9
        [
          Cbor.int body;
          encode_operand instance environment;
          encode_operand instance first;
          encode_operand instance last;
        ]

let encode_terminator instance terminator =
  let operand = encode_operand instance in
  let cases encode_item cases =
    list (fun (value, block) -> Cbor.Array [ encode_item value; Cbor.int block ]) cases
  in
  let block = option Cbor.int in
  match terminator with
  | Goto block_index -> tagged 0 [ Cbor.int block_index ]
  | Switch { value; cases = c_type; default } ->
      tagged 1
        [
          operand value; cases (fun variant_name -> Cbor.Integer variant_name) c_type; block default;
        ]
  | Switch_variant { place; cases = c_type; default } ->
      tagged 2
        [
          encode_place instance place;
          cases (fun variant_name -> Cbor.Text variant_name) c_type;
          block default;
        ]
  | Return value -> tagged 3 [ option operand value ]
  | Unreachable -> tagged 4 []
  | Fail { failure; message; length; site; caller } ->
      tagged 5
        [
          Cbor.int (match failure with Panic -> 0 | Assertion -> 1 | Todo -> 2);
          operand message;
          operand length;
          instance.path site.definition;
          Cbor.int site.line;
          Cbor.int site.column;
          option operand caller;
        ]
  | Yield { value; resume; stop } -> tagged 6 [ operand value; Cbor.int resume; block stop ]
  | Loop_call { loop; target; arguments; go_on; body; after; exit } ->
      tagged 7
        [
          Cbor.int loop;
          encode_target instance target;
          list operand arguments;
          encode_ty instance go_on;
          Cbor.int body;
          Cbor.int after;
          Cbor.int exit;
        ]
  | Loop_next { loop; body; after } -> tagged 8 [ Cbor.int loop; Cbor.int body; Cbor.int after ]

let encode_function instance (encode_item : function_) =
  Cbor.Array
    [
      list Cbor.int encode_item.parameters;
      option Cbor.int encode_item.written_result;
      option (encode_ty instance) encode_item.result;
      Bool encode_item.returns;
      list
        (fun (local : local_info) ->
          Cbor.Array
            [
              encode_ty instance local.ty;
              option (fun tag -> Cbor.Text tag) local.name;
              Bool local.borrowed;
            ])
        (Array.to_list encode_item.locals);
      list
        (fun (block_index : basic_block) ->
          Cbor.Array
            [
              list (encode_statement instance) block_index.statements;
              encode_terminator instance block_index.terminator;
            ])
        (Array.to_list encode_item.blocks);
      list
        (fun (name, ty) -> Cbor.Array [ Text name; encode_ty instance ty ])
        encode_item.environment;
    ]

let encode ?(path = Ground.encode_path) ?instance lir =
  let instance = match instance with Some instance -> instance | None -> Instance.encode ~path in
  let encoders = { path; instance } in
  Cbor.Array
    [
      instance lir.key;
      encode_function encoders lir.main;
      list (encode_function encoders) (Array.to_list lir.nested);
    ]

let rec encode_static (pointee_encoder : encoders) = function
  | Static_scalar constant -> tagged 0 [ encode_constant pointee_encoder constant ]
  | Static_record fields ->
      tagged 1
        [
          list
            (fun (name, variant_name) ->
              Cbor.Array [ Text name; encode_static pointee_encoder variant_name ])
            fields;
        ]
  | Static_variant (variant, fields) ->
      tagged 2
        [
          Text variant;
          list
            (fun (name, variant_name) ->
              Cbor.Array [ Text name; encode_static pointee_encoder variant_name ])
            fields;
        ]
  | Static_array values -> tagged 3 [ list (encode_static pointee_encoder) values ]
  | Static_storage { element; elements; owned } ->
      tagged 4
        [
          Ground.encode ~path:pointee_encoder.path element;
          list (encode_static pointee_encoder) elements;
          Bool owned;
        ]

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
      option path table.capability;
      list
        (fun (key, lir_signature) ->
          Cbor.Array [ instance key; encode_signature encoders_default lir_signature ])
        table.entries;
    ]

let derive_lir_hash = Blake3.derive_key ~context:"truss 2026-11-12 lir instance"

let hash lir =
  derive_lir_hash (Cbor.encode (Cbor.Array [ Cbor.int version; encode (canonical_instance lir) ]))
