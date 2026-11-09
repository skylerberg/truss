type local = int
type block = int

(* The type of a local, a parameter, or a result. *)
type ty =
  | Value of Ground.ty
  | Pointer of { target : ty; writable : bool }
      (** A [restrict] pointer: to a [mut] or large parameter, or to a part of one *)
  | Raw of Memory_layout.scalar  (** A scalar no Truss type names, such as a drop flag *)
  | Environment of int
      (** The environment [struct] of nested function [n] of this instance, whose fields its
          [environment] lists *)

(* A place: a local or a constant's static data, then fields, elements, and
   dereferences. *)
type root = Local of local | Static of { key : Instance.key; ty : Ground.ty }

type place = { root : root; projections : projection list }

and projection =
  | Field of string  (** A record's field *)
  | Variant_field of { variant : string; field : string }
      (** A field of a sum type's variant, which must be the variant the value holds. For an
          [indirect] variant this reaches into its block. *)
  | Index of operand  (** An element of an [Array] or of the buffer a pointer points at *)
  | Deref

and operand =
  | Copy of place  (** For a value that copies implicitly *)
  | Move of place  (** Leaves the place with nothing to drop *)
  | Constant of constant
  | Address of { place : place; writable : bool }

and constant =
  | Integer of Memory_layout.integer * Z.t
  | Float32 of int32  (** The bits *)
  | Float64 of int64  (** The bits *)
  | Bool of bool
  | Character of int
  | Bytes of string  (** The address of static bytes, such as a string literal's *)
  | Null

and function_ref =
  | Instance of Instance.key
  | Nested of int  (** A lambda or loop body of this instance *)

(* How a function is called, which the caller needs to declare it. *)
type signature = { parameters : ty list; result : ty option; returns : bool }
(** [returns] is false for a function whose result type is [Never] *)

type unary = Negate | Not | Complement

type binary =
  | Add
  | Subtract
  | Multiply
  | Divide
  | Remainder
  | Bit_and
  | Bit_or
  | Bit_xor
  | Shift_left  (** The amount is masked to the width of the value *)
  | Shift_right  (** Arithmetic on signed integers, logical on unsigned *)
  | Equal  (** On floats, every NaN equals every NaN, as DESIGN.md's lawful equality says *)
  | Not_equal
  | Less  (** On floats, NaN comes after every number *)
  | Less_equal
  | Greater
  | Greater_equal
  | Ieee_equal  (** The IEEE comparisons, on floats only *)
  | Ieee_less
  | Ieee_less_equal

(* The operations the intrinsic module lowers to directly. See CODEGEN.md,
   "The system interface". Operating-system calls are added with the
   standard library's real implementations. *)
type intrinsic =
  | Allocate
      (** [(size: USize, alignment: USize) -> pointer]; ends the process when memory runs out *)
  | Reallocate  (** [(pointer, old size, new size, alignment) -> pointer] *)
  | Free  (** [(pointer)] *)
  | Copy_bytes  (** [(destination, source, count)], which must not overlap *)
  | Move_bytes  (** [(destination, source, count)] *)
  | Compare_bytes  (** [(first, second, count) -> Int32] *)
  | Add_overflow  (** [(left, right, result pointer) -> Bool], true when it overflowed *)
  | Subtract_overflow
  | Multiply_overflow
  | Leading_zeros
  | Trailing_zeros
  | Count_ones
  | Swap_bytes
  | Rotate_left
  | Rotate_right
  | Multiply_high  (** The upper half of the full-width product *)
  | Square_root
  | Fused_multiply_add
  | Floor
  | Ceiling
  | Truncate
  | Round_even
  | Float_bits  (** A float's bits, with every NaN replaced by one canonical NaN *)
  | Float_from_bits

type target =
  | Direct of { function_ : function_ref; signature : signature }
  | Indirect of { value : operand; signature : signature }
      (** A call through a function value: its code with its environment first *)
  | Intrinsic of intrinsic

type rvalue =
  | Use of operand
  | Unary of unary * operand
  | Binary of binary * operand * operand
  | Convert of operand * Memory_layout.scalar
      (** A conversion between built-in numbers, which the type checker or the prover has shown
          keeps the value *)
  | Build of { ty : Ground.ty; variant : string option; fields : (string * operand) list }
      (** A record or a variant. Building an [indirect] variant allocates its block. *)
  | Is_variant of place * string  (** Whether a sum type's value holds the variant *)
  | Function_value of { code : function_ref; environment : operand option }

(* A position within the instance's definition, which its anchor turns into
   a file and line. See CODEGEN.md, "Positions". *)
type site = { line : int; column : int }

type statement =
  | Assign of place * rvalue
  | Call of { target : target; arguments : operand list; result : place option }
  | Drop of place  (** Runs the type's drop code *)

type terminator =
  | Goto of block
  | Switch of { value : operand; cases : (Z.t * block) list; default : block option }
      (** On an integer, a [Bool], or a [Character]; with no default, the cases cover every value *)
  | Switch_variant of { place : place; cases : (string * block) list; default : block option }
  | Return of operand option
  | Unreachable  (** A point the prover has shown is never reached *)
  | Panic of { message : operand; length : operand; site : site }
      (** Ends the process: the message is a pointer to UTF-8 bytes and their length *)
  | Yield of { value : operand; resume : block; stop : block option }
      (** Before yield lowering only. [stop] runs when the caller leaves the loop at this [yield]; a
          lending method's [yield] has none, since it always continues. *)

type basic_block = { statements : statement list; terminator : terminator }
type local_info = { ty : ty; name : string option }

type function_ = {
  parameters : local list;  (** Locals that arrive as the parameters, in order *)
  result : ty option;
  returns : bool;
  locals : local_info array;
  blocks : basic_block array;  (** Block 0 is the entry *)
  environment : (string * ty) list;
      (** For a nested function, the fields of its environment: a pointer to each local of the
          function around it that it reads, and for a loop body the slots it reports through *)
}

type t = { key : Instance.key; main : function_; nested : function_ array }

let signature (f : function_) =
  {
    parameters = List.map (fun local -> f.locals.(local).ty) f.parameters;
    result = f.result;
    returns = f.returns;
  }

let successors = function
  | Goto block -> [ block ]
  | Switch { cases; default; _ } -> List.map snd cases @ Option.to_list default
  | Switch_variant { cases; default; _ } -> List.map snd cases @ Option.to_list default
  | Return _ | Unreachable | Panic _ -> []
  | Yield { resume; stop; _ } -> resume :: Option.to_list stop

(* Blocks in reverse postorder of a depth-first walk that takes successors
   in order. *)
let reverse_postorder (blocks : basic_block array) =
  let visited = Array.make (Array.length blocks) false in
  let order = ref [] in
  let rec visit block =
    if not visited.(block) then begin
      visited.(block) <- true;
      List.iter visit (successors blocks.(block).terminator);
      order := block :: !order
    end
  in
  if Array.length blocks > 0 then visit 0;
  !order

let rec map_place map_local map_block (place : place) =
  let root =
    match place.root with Local local -> Local (map_local local) | Static _ as root -> root
  in
  { root; projections = List.map (map_projection map_local map_block) place.projections }

and map_projection map_local map_block = function
  | Index operand -> Index (map_operand map_local map_block operand)
  | (Field _ | Variant_field _ | Deref) as projection -> projection

and map_operand map_local map_block = function
  | Copy place -> Copy (map_place map_local map_block place)
  | Move place -> Move (map_place map_local map_block place)
  | Address { place; writable } -> Address { place = map_place map_local map_block place; writable }
  | Constant _ as operand -> operand

let map_rvalue map_local map_block rvalue =
  let operand = map_operand map_local map_block in
  match rvalue with
  | Use o -> Use (operand o)
  | Unary (op, o) -> Unary (op, operand o)
  | Binary (op, a, b) -> Binary (op, operand a, operand b)
  | Convert (o, scalar) -> Convert (operand o, scalar)
  | Build { ty; variant; fields } ->
      Build { ty; variant; fields = List.map (fun (name, o) -> (name, operand o)) fields }
  | Is_variant (place, variant) -> Is_variant (map_place map_local map_block place, variant)
  | Function_value { code; environment } ->
      Function_value { code; environment = Option.map operand environment }

let map_target map_local map_block = function
  | Indirect { value; signature } ->
      Indirect { value = map_operand map_local map_block value; signature }
  | (Direct _ | Intrinsic _) as target -> target

let map_statement map_local map_block = function
  | Assign (place, rvalue) ->
      Assign (map_place map_local map_block place, map_rvalue map_local map_block rvalue)
  | Call { target; arguments; result } ->
      Call
        {
          target = map_target map_local map_block target;
          arguments = List.map (map_operand map_local map_block) arguments;
          result = Option.map (map_place map_local map_block) result;
        }
  | Drop place -> Drop (map_place map_local map_block place)

let map_terminator map_local map_block terminator =
  let operand = map_operand map_local map_block in
  match terminator with
  | Goto block -> Goto (map_block block)
  | Switch { value; cases; default } ->
      Switch
        {
          value = operand value;
          cases = List.map (fun (value, block) -> (value, map_block block)) cases;
          default = Option.map map_block default;
        }
  | Switch_variant { place; cases; default } ->
      Switch_variant
        {
          place = map_place map_local map_block place;
          cases = List.map (fun (variant, block) -> (variant, map_block block)) cases;
          default = Option.map map_block default;
        }
  | Return value -> Return (Option.map operand value)
  | Unreachable -> Unreachable
  | Panic { message; length; site } ->
      Panic { message = operand message; length = operand length; site }
  | Yield { value; resume; stop } ->
      Yield { value = operand value; resume = map_block resume; stop = Option.map map_block stop }

let canonical (f : function_) =
  let order = reverse_postorder f.blocks in
  let block_number = Array.make (Array.length f.blocks) (-1) in
  List.iteri (fun index block -> block_number.(block) <- index) order;
  let local_number = Array.make (Array.length f.locals) (-1) in
  let next = ref 0 in
  let number local =
    if local_number.(local) < 0 then begin
      local_number.(local) <- !next;
      incr next
    end;
    local
  in
  List.iter (fun local -> ignore (number local)) f.parameters;
  let identity block = block in
  List.iter
    (fun block ->
      let { statements; terminator } = f.blocks.(block) in
      List.iter (fun statement -> ignore (map_statement number identity statement)) statements;
      ignore (map_terminator number identity terminator))
    order;
  let locals = Array.make !next { ty = Raw Bool; name = None } in
  Array.iteri (fun old index -> if index >= 0 then locals.(index) <- f.locals.(old)) local_number;
  let map_local local = local_number.(local) in
  let map_block block = block_number.(block) in
  let blocks =
    Array.of_list
      (List.map
         (fun block ->
           let { statements; terminator } = f.blocks.(block) in
           {
             statements = List.map (map_statement map_local map_block) statements;
             terminator = map_terminator map_local map_block terminator;
           })
         order)
  in
  { f with parameters = List.map map_local f.parameters; locals; blocks }

let canonical_instance t = { t with main = canonical t.main; nested = Array.map canonical t.nested }

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

let statement_to_string = function
  | Assign (place, rvalue) -> place_to_string place ^ " = " ^ rvalue_to_string rvalue
  | Call { target; arguments; result } ->
      (match result with None -> "" | Some place -> place_to_string place ^ " = ")
      ^ "call " ^ target_to_string target ^ "("
      ^ String.concat ", " (List.map operand_to_string arguments)
      ^ ")"
  | Drop place -> "drop " ^ place_to_string place

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
  | Panic { message; length; _ } ->
      "panic(" ^ operand_to_string message ^ ", " ^ operand_to_string length ^ ")"
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
