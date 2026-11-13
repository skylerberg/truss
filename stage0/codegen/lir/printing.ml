(* The LIR as text, for reading and for tests. *)

open Ir

let scalar_name = function
  | Memory_layout.Nullable_pointer _ -> "nullable"
  | scalar -> Memory_layout.scalar_to_string scalar

let rec ty_to_string = function
  | Value ty -> Ground.to_string ty
  | Pointer { target; writable } -> (if writable then "*mut " else "*") ^ ty_to_string target
  | Raw scalar -> "raw " ^ scalar_name scalar
  | Environment nested_index -> Printf.sprintf "environment %d" nested_index
  | Evidence nested_index -> Printf.sprintf "evidence %d" nested_index

let function_ref_to_string = function
  | Instance key -> Instance.to_string key
  | Nested nested_index -> Printf.sprintf "nested %d" nested_index

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
  | Evidence_fill -> "evidence_fill"
  | Environment -> "environment"
  | Run_test -> "run_test"
  | Report_tests_to -> "report_tests_to"
  | Live_blocks -> "live_blocks"
  | Terminated_length -> "terminated_length"
  | Evidence_implementation -> "evidence_implementation"
  | Evidence_outer -> "evidence_outer"
  | Program_argument -> "program_argument"
  | Coroutine_start -> "coroutine_start"
  | Coroutine_resume -> "coroutine_resume"
  | Coroutine_suspend -> "coroutine_suspend"
  | Tasks_spawn -> "tasks_spawn"
  | Shared_allocate -> "shared_allocate"
  | Shared_retain -> "shared_retain"
  | Shared_release -> "shared_release"
  | Shared_free -> "shared_free"
  | Shared_lock -> "shared_lock"
  | Shared_unlock -> "shared_unlock"
  | Blocking_begin -> "blocking_begin"
  | Blocking_end -> "blocking_end"

let rvalue_to_string = function
  | Use operand -> operand_to_string operand
  | Unary (op, operand) -> unary_name op ^ operand_to_string operand
  | Binary (op, left, right) ->
      operand_to_string left ^ " " ^ binary_name op ^ " " ^ operand_to_string right
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
      ^
      match environment with
      | None -> ""
      | Some environment_operand -> " with " ^ operand_to_string environment_operand)

let target_to_string = function
  | Direct { function_; _ } -> function_ref_to_string function_
  | Indirect { value; _ } -> "(" ^ operand_to_string value ^ ")"
  | Intrinsic intrinsic -> "intrinsic " ^ intrinsic_name intrinsic
  | Foreign declaration -> "foreign " ^ declaration.symbol
  | Evidence_call { evidence; capability; slot; _ } ->
      Printf.sprintf "(%s %s %d)" (operand_to_string evidence) (Ground.path_name capability) slot
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
  | Region { fork; region = Branch } -> Printf.sprintf "region of fork %d" fork
  | Region { fork; region = Chunk { first; last } } ->
      Printf.sprintf "region of fork %d for %s to %s" fork
        (place_to_string (local_place first))
        (place_to_string (local_place last))
  | Region { fork; region = Task { function_value; item } } ->
      Printf.sprintf "region of fork %d as a task %s given %s" fork
        (place_to_string (local_place function_value))
        (place_to_string (local_place item))
  | Regions_end { fork } -> Printf.sprintf "end of fork %d" fork
  | Loop_body { loop; part } ->
      Printf.sprintf "body of loop %d%s" loop
        (match part with Some part -> " given " ^ place_to_string (local_place part) | None -> "")
  | Loop_exit { loop } -> Printf.sprintf "exit of loop %d" loop
  | Fork { branches } ->
      "fork "
      ^ String.concat ", "
          (List.map
             (fun (nested, environment) ->
               Printf.sprintf "nested %d(%s)" nested (operand_to_string environment))
             branches)
  | Fork_range { body; environment; first; last } ->
      Printf.sprintf "fork nested %d(%s) over %s to %s" body (operand_to_string environment)
        (operand_to_string first) (operand_to_string last)

let terminator_to_string = function
  | Goto block -> Printf.sprintf "goto b%d" block
  | Switch { value; cases; default } ->
      "switch " ^ operand_to_string value ^ " ["
      ^ String.concat ", "
          (List.map
             (fun (case_value, block_index) ->
               Printf.sprintf "%s => b%d" (Z.to_string case_value) block_index)
             cases)
      ^ (match default with
        | None -> ""
        | Some block_index -> Printf.sprintf ", _ => b%d" block_index)
      ^ "]"
  | Switch_variant { place; cases; default } ->
      "switch " ^ place_to_string place ^ " ["
      ^ String.concat ", "
          (List.map
             (fun (case_value, block_index) -> Printf.sprintf "%s => b%d" case_value block_index)
             cases)
      ^ (match default with
        | None -> ""
        | Some block_index -> Printf.sprintf ", _ => b%d" block_index)
      ^ "]"
  | Return None -> "return"
  | Return (Some operand) -> "return " ^ operand_to_string operand
  | Unreachable -> "unreachable"
  | Fail { failure; message; length; _ } ->
      (match failure with Panic -> "panic(" | Assertion -> "assertion failed(" | Todo -> "todo(")
      ^ operand_to_string message ^ ", " ^ operand_to_string length ^ ")"
  | Yield { value; resume; stop } ->
      Printf.sprintf "yield %s resume b%d%s" (operand_to_string value) resume
        (match stop with None -> "" | Some block_index -> Printf.sprintf " stop b%d" block_index)
  | Loop_call { loop; target; arguments; body; after; exit; _ } ->
      Printf.sprintf "loop %d: call %s(%s) body b%d after b%d exit %s" loop
        (target_to_string target)
        (String.concat ", " (List.map operand_to_string arguments))
        body after
        (place_to_string (local_place exit))
  | Loop_next { loop; body; after } ->
      Printf.sprintf "next of loop %d body b%d after b%d" loop body after

let function_to_string (function_ : function_) =
  let parameters =
    String.concat ", "
      (List.map
         (fun local -> Printf.sprintf "_%d: %s" local (ty_to_string function_.locals.(local).ty))
         function_.parameters)
  in
  let header =
    Printf.sprintf "fn(%s)%s%s" parameters
      (match function_.result with None -> "" | Some ty -> " -> " ^ ty_to_string ty)
      (if function_.returns then "" else " never")
  in
  let blocks =
    List.mapi
      (fun index { statements; terminator } ->
        Printf.sprintf "b%d: %s" index
          (String.concat "; "
             (List.map statement_to_string statements @ [ terminator_to_string terminator ])))
      (Array.to_list function_.blocks)
  in
  String.concat "\n" (header :: blocks)

let to_string lir =
  String.concat "\n"
    ((Instance.to_string lir.key ^ " " ^ function_to_string lir.main)
    :: List.mapi
         (fun position function_ ->
           Printf.sprintf "nested %d %s" position (function_to_string function_))
         (Array.to_list lir.nested))
