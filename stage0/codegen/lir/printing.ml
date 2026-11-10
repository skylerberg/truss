(* The LIR as text, for reading and for tests. *)

open Ir

(* Printing *)

let integer_name = function
  | Memory_layout.Int8 -> "Int8"
  | Int16 -> "Int16"
  | Int32 -> "Int32"
  | Int64 -> "Int64"
  | UInt8 -> "UInt8"
  | UInt16 -> "UInt16"
  | UInt32 -> "UInt32"
  | UInt64 -> "UInt64"
  | USize -> "USize"
  | ISize -> "ISize"

let scalar_name = function
  | Memory_layout.Integer integer -> integer_name integer
  | Float32 -> "Float32"
  | Float64 -> "Float64"
  | Bool -> "Bool"
  | Character -> "Character"
  | Pointer _ -> "pointer"
  | Nullable_pointer _ -> "nullable"

let rec ty_to_string = function
  | Value ty -> Ground.to_string ty
  | Pointer { target; writable } -> (if writable then "*mut " else "*") ^ ty_to_string target
  | Raw scalar -> "raw " ^ scalar_name scalar
  | Environment n -> Printf.sprintf "environment %d" n
  | Evidence n -> Printf.sprintf "evidence %d" n

let function_ref_to_string = function
  | Instance key -> Instance.to_string key
  | Nested n -> Printf.sprintf "nested %d" n

let constant_to_string = function
  | Integer (_, value) -> Z.to_string value
  | Float32 bits -> Printf.sprintf "%g" (Int32.float_of_bits bits)
  | Float64 bits -> Printf.sprintf "%g" (Int64.float_of_bits bits)
  | Bool value -> string_of_bool value
  | Character code -> Printf.sprintf "U+%04X" code
  | Bytes text -> Printf.sprintf "%S" text
  | Null -> "null"
  | Symbol_address key -> "&" ^ Instance.to_string key
  | Size_of ty -> "size_of(" ^ Ground.to_string ty ^ ")"
  | Alignment_of ty -> "alignment_of(" ^ Ground.to_string ty ^ ")"

let rec place_to_string (place : place) =
  List.fold_left
    (fun text projection ->
      match projection with
      | Field name -> text ^ "." ^ name
      | Variant_field { variant; field } -> text ^ "." ^ variant ^ "." ^ field
      | Index operand -> text ^ "[" ^ operand_to_string operand ^ "]"
      | Deref -> "*" ^ text)
    (match place.root with
    | Local local -> Printf.sprintf "_%d" local
    | Static { key; _ } -> Instance.to_string key)
    place.projections

and operand_to_string = function
  | Copy place -> place_to_string place
  | Move place -> "move " ^ place_to_string place
  | Constant constant -> constant_to_string constant
  | Address { place; writable } -> (if writable then "&mut " else "&") ^ place_to_string place
  | Moved_address place -> "&own " ^ place_to_string place

let unary_name = function Negate -> "-" | Not -> "!" | Complement -> "~"

let binary_name = function
  | Add -> "+"
  | Subtract -> "-"
  | Multiply -> "*"
  | Divide -> "/"
  | Remainder -> "%"
  | Bit_and -> "&"
  | Bit_or -> "|"
  | Bit_xor -> "^"
  | Shift_left -> "<<"
  | Shift_right -> ">>"
  | Equal -> "=="
  | Not_equal -> "!="
  | Less -> "<"
  | Less_equal -> "<="
  | Greater -> ">"
  | Greater_equal -> ">="
  | Ieee_equal -> "ieee=="
  | Ieee_less -> "ieee<"
  | Ieee_less_equal -> "ieee<="

let intrinsic_name = function
  | Allocate -> "allocate"
  | Reallocate -> "reallocate"
  | Free -> "free"
  | Copy_bytes -> "copy_bytes"
  | Move_bytes -> "move_bytes"
  | Compare_bytes -> "compare_bytes"
  | Add_overflow -> "add_overflow"
  | Subtract_overflow -> "subtract_overflow"
  | Multiply_overflow -> "multiply_overflow"
  | Leading_zeros -> "leading_zeros"
  | Trailing_zeros -> "trailing_zeros"
  | Count_ones -> "count_ones"
  | Swap_bytes -> "swap_bytes"
  | Rotate_left -> "rotate_left"
  | Rotate_right -> "rotate_right"
  | Multiply_high -> "multiply_high"
  | Square_root -> "square_root"
  | Fused_multiply_add -> "fused_multiply_add"
  | Floor -> "floor"
  | Ceiling -> "ceiling"
  | Truncate -> "truncate"
  | Round_even -> "round_even"
  | Float_bits -> "float_bits"
  | Float_from_bits -> "float_from_bits"
  | Float_text -> "float_text"
  | Evidence_fill -> "evidence_fill"
  | Environment -> "environment"
  | Terminated_length -> "terminated_length"
  | Debug_begin -> "debug_begin"
  | Debug_text -> "debug_text"
  | Debug_signed -> "debug_signed"
  | Debug_unsigned -> "debug_unsigned"
  | Debug_float32 -> "debug_float32"
  | Debug_float64 -> "debug_float64"
  | Debug_bool -> "debug_bool"
  | Debug_character -> "debug_character"
  | Debug_string -> "debug_string"
  | Debug_bytes -> "debug_bytes"
  | Debug_length -> "debug_length"
  | Evidence_implementation -> "evidence_implementation"
  | Evidence_outer -> "evidence_outer"
  | Program_argument -> "program_argument"

let rvalue_to_string = function
  | Use operand -> operand_to_string operand
  | Unary (op, operand) -> unary_name op ^ operand_to_string operand
  | Binary (op, a, b) -> operand_to_string a ^ " " ^ binary_name op ^ " " ^ operand_to_string b
  | Convert (operand, scalar) -> scalar_name scalar ^ "(" ^ operand_to_string operand ^ ")"
  | Build { ty; variant; fields } ->
      Ground.to_string ty
      ^ (match variant with None -> "" | Some variant -> "." ^ variant)
      ^ "("
      ^ String.concat ", "
          (List.map (fun (name, operand) -> name ^ ": " ^ operand_to_string operand) fields)
      ^ ")"
  | Is_variant (place, variant) -> place_to_string place ^ " is " ^ variant
  | Function_value { code; environment } -> (
      "fn " ^ function_ref_to_string code
      ^ match environment with None -> "" | Some e -> " with " ^ operand_to_string e)

let target_to_string = function
  | Direct { function_; _ } -> function_ref_to_string function_
  | Indirect { value; _ } -> "(" ^ operand_to_string value ^ ")"
  | Intrinsic intrinsic -> "intrinsic " ^ intrinsic_name intrinsic
  | Foreign declaration -> "foreign " ^ declaration.symbol
  | Evidence_call { evidence; slot; _ } ->
      Printf.sprintf "(%s table %d)" (operand_to_string evidence) slot
  | Table_call { table; value; slot; _ } ->
      Printf.sprintf "(%s[%d] %s)" (operand_to_string table) slot (operand_to_string value)

let statement_to_string = function
  | Assign (place, rvalue) -> place_to_string place ^ " = " ^ rvalue_to_string rvalue
  | Call { target; arguments; result } ->
      (match result with Returned place -> place_to_string place ^ " = " | _ -> "")
      ^ "call " ^ target_to_string target ^ "("
      ^ String.concat ", "
          ((match result with Written place -> [ "out " ^ place_to_string place ] | _ -> [])
          @ List.map operand_to_string arguments)
      ^ ")"
  | Drop place -> "drop " ^ place_to_string place
  | Free_block { place; variant } -> "free " ^ place_to_string place ^ "." ^ variant
  | Echo { text; length; _ } ->
      "echo(" ^ operand_to_string text ^ ", " ^ operand_to_string length ^ ")"

let terminator_to_string = function
  | Goto block -> Printf.sprintf "goto b%d" block
  | Switch { value; cases; default } ->
      "switch " ^ operand_to_string value ^ " ["
      ^ String.concat ", "
          (List.map (fun (v, b) -> Printf.sprintf "%s => b%d" (Z.to_string v) b) cases)
      ^ (match default with None -> "" | Some b -> Printf.sprintf ", _ => b%d" b)
      ^ "]"
  | Switch_variant { place; cases; default } ->
      "switch " ^ place_to_string place ^ " ["
      ^ String.concat ", " (List.map (fun (v, b) -> Printf.sprintf "%s => b%d" v b) cases)
      ^ (match default with None -> "" | Some b -> Printf.sprintf ", _ => b%d" b)
      ^ "]"
  | Return None -> "return"
  | Return (Some operand) -> "return " ^ operand_to_string operand
  | Unreachable -> "unreachable"
  | Fail { failure; message; length; _ } ->
      (match failure with Panic -> "panic(" | Assertion -> "assertion failed(" | Todo -> "todo(")
      ^ operand_to_string message ^ ", " ^ operand_to_string length ^ ")"
  | Yield { value; resume; stop } ->
      Printf.sprintf "yield %s resume b%d%s" (operand_to_string value) resume
        (match stop with None -> "" | Some b -> Printf.sprintf " stop b%d" b)

let function_to_string (f : function_) =
  let parameters =
    String.concat ", "
      (List.map
         (fun local -> Printf.sprintf "_%d: %s" local (ty_to_string f.locals.(local).ty))
         f.parameters)
  in
  let header =
    Printf.sprintf "fn(%s)%s%s" parameters
      (match f.result with None -> "" | Some ty -> " -> " ^ ty_to_string ty)
      (if f.returns then "" else " never")
  in
  let blocks =
    List.mapi
      (fun index { statements; terminator } ->
        Printf.sprintf "b%d: %s" index
          (String.concat "; "
             (List.map statement_to_string statements @ [ terminator_to_string terminator ])))
      (Array.to_list f.blocks)
  in
  String.concat "\n" (header :: blocks)

let to_string t =
  String.concat "\n"
    ((Instance.to_string t.key ^ " " ^ function_to_string t.main)
    :: List.mapi
         (fun i f -> Printf.sprintf "nested %d %s" i (function_to_string f))
         (Array.to_list t.nested))
