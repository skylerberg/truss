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
type site = { definition : Path.t; line : int; column : int }

type statement =
  | Assign of place * rvalue
  | Call of { target : target; arguments : operand list; result : place option }
  | Drop of place  (** Runs the type's drop code *)
  | Free_block of { place : place; variant : string }
      (** Frees the block of an [indirect] variant whose fields have all been moved out or dropped
      *)

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

let bug format = Printf.ksprintf (fun message -> invalid_arg ("Lir: " ^ message)) format

let erased env = function
  | Value ty -> (Memory_layout.of_type env ty).size = 0
  | Pointer _ | Raw _ | Environment _ -> false

let member_ty : Memory_layout.member -> ty = function
  | Typed ty -> Value ty
  | Raw scalar -> Raw scalar

let find_field (fields : Memory_layout.field list) name =
  List.find_map
    (fun (field : Memory_layout.field) ->
      if field.name = name then Some (member_ty field.member) else None)
    fields

let struct_field (layout : Memory_layout.t) name =
  match layout.form with Struct fields -> find_field fields name | _ -> None

let variant_field_type env sum variant field =
  let layout = Memory_layout.of_type env sum in
  let in_payload (payload : Memory_layout.t) =
    match payload.form with
    | Struct fields -> find_field fields field
    | Scalar (Pointer (Block _)) -> struct_field (Memory_layout.block env sum variant) field
    | _ -> None
  in
  match layout.form with
  | Tagged { variants; _ } -> (
      match List.find_opt (fun (v : Memory_layout.variant) -> v.name = variant) variants with
      | Some v -> in_payload v.payload
      | None -> bug "%s has no variant %s" (Ground.to_string sum) variant)
  | Niche_encoded { dataful; _ } when dataful.name = variant -> in_payload dataful.payload
  | Niche_encoded _ | Tag_only _ | Zero_size -> None
  | _ -> bug "a variant of %s, which is not a sum type" (Ground.to_string sum)

let projection_type env ~environment ty projection =
  let result =
    match (projection, ty) with
    | Deref, Pointer { target; _ } -> Some target
    | Deref, Raw (Pointer (Data target) | Nullable_pointer (Data target)) -> Some (Value target)
    | Field name, Value record -> (
        let layout = Memory_layout.of_type env record in
        match layout.form with
        | Struct _ -> struct_field layout name
        | Zero_size -> None
        | _ -> bug "field %s of %s, which is not a record" name (Ground.to_string record))
    | Field name, Environment n -> (
        match List.assoc_opt name (environment n) with
        | Some ty -> Some ty
        | None -> bug "environment %d has no field %s" n name)
    | Variant_field { variant; field }, Value sum -> variant_field_type env sum variant field
    | Index _, Value array -> (
        match (Memory_layout.of_type env array).form with
        | Array { element; _ } -> Some (Value element)
        | Zero_size -> None
        | _ -> bug "an index into %s" (Ground.to_string array))
    | Index _, Raw (Pointer (Data element) | Nullable_pointer (Data element)) ->
        Some (Value element)
    | _ -> bug "a projection that does not fit its place"
  in
  match result with Some ty when erased env ty -> None | other -> other

let place_type env ~environment (f : function_) (place : place) =
  let root =
    match place.root with Local local -> f.locals.(local).ty | Static { ty; _ } -> Value ty
  in
  if erased env root then None
  else
    List.fold_left
      (fun ty projection ->
        Option.bind ty (fun ty -> projection_type env ~environment ty projection))
      (Some root) place.projections

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

(* Rewrites every place, each after the places in its indexes, and every
   block number. *)
let rec map_place ~place ~block (p : place) =
  place { p with projections = List.map (map_projection ~place ~block) p.projections }

and map_projection ~place ~block = function
  | Index operand -> Index (map_operand ~place ~block operand)
  | (Field _ | Variant_field _ | Deref) as projection -> projection

and map_operand ~place ~block = function
  | Copy p -> Copy (map_place ~place ~block p)
  | Move p -> Move (map_place ~place ~block p)
  | Address { place = p; writable } -> Address { place = map_place ~place ~block p; writable }
  | Constant _ as operand -> operand

let map_rvalue ~place ~block rvalue =
  let operand = map_operand ~place ~block in
  match rvalue with
  | Use o -> Use (operand o)
  | Unary (op, o) -> Unary (op, operand o)
  | Binary (op, a, b) -> Binary (op, operand a, operand b)
  | Convert (o, scalar) -> Convert (operand o, scalar)
  | Build { ty; variant; fields } ->
      Build { ty; variant; fields = List.map (fun (name, o) -> (name, operand o)) fields }
  | Is_variant (p, variant) -> Is_variant (map_place ~place ~block p, variant)
  | Function_value { code; environment } ->
      Function_value { code; environment = Option.map operand environment }

let map_target ~place ~block = function
  | Indirect { value; signature } -> Indirect { value = map_operand ~place ~block value; signature }
  | (Direct _ | Intrinsic _) as target -> target

let map_statement ~place ~block = function
  | Assign (p, rvalue) -> Assign (map_place ~place ~block p, map_rvalue ~place ~block rvalue)
  | Call { target; arguments; result } ->
      Call
        {
          target = map_target ~place ~block target;
          arguments = List.map (map_operand ~place ~block) arguments;
          result = Option.map (map_place ~place ~block) result;
        }
  | Drop p -> Drop (map_place ~place ~block p)
  | Free_block { place = p; variant } -> Free_block { place = map_place ~place ~block p; variant }

let map_terminator ~place ~block terminator =
  let operand = map_operand ~place ~block in
  match terminator with
  | Goto b -> Goto (block b)
  | Switch { value; cases; default } ->
      Switch
        {
          value = operand value;
          cases = List.map (fun (value, b) -> (value, block b)) cases;
          default = Option.map block default;
        }
  | Switch_variant { place = p; cases; default } ->
      Switch_variant
        {
          place = map_place ~place ~block p;
          cases = List.map (fun (variant, b) -> (variant, block b)) cases;
          default = Option.map block default;
        }
  | Return value -> Return (Option.map operand value)
  | Unreachable -> Unreachable
  | Panic { message; length; site } ->
      Panic { message = operand message; length = operand length; site }
  | Yield { value; resume; stop } ->
      Yield { value = operand value; resume = block resume; stop = Option.map block stop }

let rename map_local (p : place) =
  match p.root with Local local -> { p with root = Local (map_local local) } | Static _ -> p

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
    (fun b ->
      let { statements; terminator } = f.blocks.(b) in
      List.iter
        (fun statement -> ignore (map_statement ~place:(rename number) ~block:identity statement))
        statements;
      ignore (map_terminator ~place:(rename number) ~block:identity terminator))
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
             statements =
               List.map (map_statement ~place:(rename map_local) ~block:map_block) statements;
             terminator = map_terminator ~place:(rename map_local) ~block:map_block terminator;
           })
         order)
  in
  { f with parameters = List.map map_local f.parameters; locals; blocks }

let canonical_instance t = { t with main = canonical t.main; nested = Array.map canonical t.nested }
let version = 1
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

let rec encode_scalar instance (scalar : Memory_layout.scalar) =
  match scalar with
  | Integer integer -> tagged 0 [ Cbor.int (integer_tag integer) ]
  | Float32 -> tagged 1 []
  | Float64 -> tagged 2 []
  | Bool -> tagged 3 []
  | Character -> tagged 4 []
  | Pointer pointee -> tagged 5 [ encode_pointee instance pointee ]
  | Nullable_pointer pointee -> tagged 6 [ encode_pointee instance pointee ]

and encode_pointee _instance : Memory_layout.pointee -> Cbor.t = function
  | Data ty -> tagged 0 [ Ground.encode ty ]
  | Block (ty, variant) -> tagged 1 [ Ground.encode ty; Text variant ]
  | Code f -> tagged 2 [ Ground.encode (Function f) ]
  | Opaque -> tagged 3 []

let rec encode_ty instance = function
  | Value ty -> tagged 0 [ Ground.encode ty ]
  | Pointer { target; writable } -> tagged 1 [ encode_ty instance target; Bool writable ]
  | Raw scalar -> tagged 2 [ encode_scalar instance scalar ]
  | Environment n -> tagged 3 [ Cbor.int n ]

let encode_function_ref instance = function
  | Instance key -> tagged 0 [ instance key ]
  | Nested n -> tagged 1 [ Cbor.int n ]

let rec encode_place instance (place : place) =
  Cbor.Array
    [
      (match place.root with
      | Local local -> tagged 0 [ Cbor.int local ]
      | Static { key; ty } -> tagged 1 [ instance key; Ground.encode ty ]);
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
  | Constant constant -> tagged 2 [ encode_constant constant ]
  | Address { place; writable } -> tagged 3 [ encode_place instance place; Bool writable ]

and encode_constant = function
  | Integer (integer, value) -> tagged 0 [ Cbor.int (integer_tag integer); Integer value ]
  | Float32 bits -> tagged 1 [ Integer (Z.of_int32_unsigned bits) ]
  | Float64 bits -> tagged 2 [ Integer (Z.of_int64_unsigned bits) ]
  | Bool value -> tagged 3 [ Bool value ]
  | Character code -> tagged 4 [ Cbor.int code ]
  | Bytes text -> tagged 5 [ Bytes text ]
  | Null -> tagged 6 []

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
          Ground.encode ty;
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

let encode_statement instance = function
  | Assign (place, rvalue) ->
      tagged 0 [ encode_place instance place; encode_rvalue instance rvalue ]
  | Call { target; arguments; result } ->
      tagged 1
        [
          encode_target instance target;
          list (encode_operand instance) arguments;
          option (encode_place instance) result;
        ]
  | Drop place -> tagged 2 [ encode_place instance place ]
  | Free_block { place; variant } -> tagged 3 [ encode_place instance place; Text variant ]

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
  | Panic { message; length; site } ->
      tagged 5
        [
          operand message;
          operand length;
          Ground.encode_path site.definition;
          Cbor.int site.line;
          Cbor.int site.column;
        ]
  | Yield { value; resume; stop } -> tagged 6 [ operand value; Cbor.int resume; block stop ]

let encode_function instance (f : function_) =
  Cbor.Array
    [
      list Cbor.int f.parameters;
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

let encode ?(instance = Instance.encode) t =
  Cbor.Array
    [
      instance t.key;
      encode_function instance t.main;
      list (encode_function instance) (Array.to_list t.nested);
    ]

let hash t =
  Blake3.hash
    (Cbor.encode (Cbor.Array [ Text "truss lir"; Cbor.int version; encode (canonical_instance t) ]))

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
  | Free_block { place; variant } -> "free " ^ place_to_string place ^ "." ^ variant

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
