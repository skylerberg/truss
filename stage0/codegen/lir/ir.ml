(* The lowered IR's types, the queries over them, mapping a function's
   places and blocks, and putting a function in canonical form. See lir.mli. *)

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
  | Evidence of int
      (** Evidence a [provide] builds on the stack, with room for [n] pointers to the evidence its
          implementation captured *)

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
  | Moved_address of place
      (** The address of a place whose value the callee takes, for a large [own] argument: the place
          holds nothing after the call *)

and constant =
  | Integer of Memory_layout.integer * Z.t
  | Float32 of int32  (** The bits *)
  | Float64 of int64  (** The bits *)
  | Bool of bool
  | Character of int
  | Bytes of string  (** The address of static bytes, such as a string literal's *)
  | Null
  | Symbol_address of Instance.key  (** The address of static evidence or a table *)
  | Size_of of Ground.ty  (** A [USize]: how many bytes a value of the type takes *)
  | Alignment_of of Ground.ty  (** A [USize]: the alignment of a value of the type *)

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
  | Grow
      (** [(buffer pointer's address, length, capacity's address, element size, alignment, minimum)]:
          gives storage room for at least [minimum] elements. Storage with capacity 0 and a nonzero
          length is static, and is copied to the heap, never freed. *)
  | System_write  (** [(descriptor, bytes, count) -> ISize], -1 on error *)
  | System_read  (** [(descriptor, bytes, count) -> ISize], -1 on error *)
  | System_environment
      (** [(name, name length, value length's address) -> bytes]: an environment variable's value,
          null when it is unset *)
  | System_open
      (** [(path, path length, flags, error's address) -> Int32]: a descriptor, -1 with the error
          number written when it fails *)
  | System_close  (** [(descriptor)] *)
  | System_run
      (** [(program, length, arguments, length, error's address) -> Int32]: as [run_process] *)
  | Float_text
      (** [(value, bytes) -> USize]: writes the shortest decimal that reads back as the float, at
          most [float_text_limit] bytes, as [Display] shows it *)
  | Clock_now  (** [() -> Int64], nanoseconds since the Unix epoch *)
  | Random_fill  (** [(bytes, count)] *)
  | Debug_begin  (** Empties the debug output buffer *)
  | Debug_text  (** [(bytes, count)]: appends text as it is *)
  | Debug_signed  (** [(Int64)] *)
  | Debug_unsigned  (** [(UInt64)] *)
  | Debug_float32
  | Debug_float64  (** The shortest decimal that reads back as the same float *)
  | Debug_bool
  | Debug_character  (** As [Character"x"] *)
  | Debug_string  (** [(bytes, count)]: as a quoted string with escapes *)
  | Debug_bytes  (** [() -> pointer] to the buffer's bytes *)
  | Debug_length  (** [() -> USize] *)
  | Evidence_implementation  (** [(evidence) -> pointer] to the value that implements it *)
  | Evidence_outer  (** [(evidence, index) -> evidence] the implementation captured *)
  | Program_argument
      (** [(arguments, index, length pointer) -> bytes]: a program argument as UTF-8, with bad
          sequences replaced by U+FFFD *)
  | Evidence_fill
      (** [(evidence's address, implementation, table, captured evidence...)]: fills evidence a
          [provide] builds *)

let float_text_limit = 32

type target =
  | Direct of { function_ : function_ref; signature : signature }
  | Indirect of { value : operand; signature : signature }
      (** A call through a function value: its code, given its environment first *)
  | Intrinsic of intrinsic
  | Evidence_call of { evidence : operand; slot : int; signature : signature }
      (** A capability's method: entry [slot] of the evidence's table, given the evidence first *)
  | Table_call of { table : operand; value : operand; slot : int; signature : signature }
      (** Entry [slot] of a table of code, such as an [any] value's, given the value first *)

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

(* Why a [fail] ends the run: a panic, a failed [assert] in a test, or a
   [todo] that was reached. *)
type failure = Panic | Assertion | Todo

(* Where a call's result goes. A target that is given something first, such
   as a function value's environment, is given it before the result's
   pointer. *)
type destination =
  | Discarded  (** There is no result, or nothing reads it *)
  | Returned of place  (** Returned by value, and written to the place *)
  | Written of place
      (** Written by the callee through a pointer to the place, the call's first argument, for a
          result too large to return *)

type statement =
  | Assign of place * rvalue
  | Call of { target : target; arguments : operand list; result : destination }
  | Drop of place  (** Runs the type's drop code *)
  | Echo of { text : operand; length : operand; site : site }
      (** Records the debug output of a value: a pointer to UTF-8 bytes and their length *)
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
  | Fail of { failure : failure; message : operand; length : operand; site : site }
      (** Ends a test or the process: the message is a pointer to UTF-8 bytes and their length *)
  | Yield of { value : operand; resume : block; stop : block option }
      (** Before yield lowering only. [stop] runs when the caller leaves the loop at this [yield]; a
          lending method's [yield] has none, since it always continues. *)

type basic_block = { statements : statement list; terminator : terminator }
type local_info = { ty : ty; name : string option }

type function_ = {
  parameters : local list;  (** Locals that arrive as the parameters, in order *)
  written_result : local option;
      (** The parameter pointing to where a result too large to return is written, which holds no
          value until the function writes it *)
  result : ty option;
  returns : bool;
  locals : local_info array;
  blocks : basic_block array;  (** Block 0 is the entry *)
  environment : (string * ty) list;
      (** For a nested function, the fields of its environment: a pointer to each local of the
          function around it that it reads, and for a loop body the slots it reports through *)
}

type t = { key : Instance.key; main : function_; nested : function_ array }

(* Static data: a constant's value, which the emitter writes as C
   initializers in a read-only place. *)
type static_value =
  | Static_scalar of constant
  | Static_record of (string * static_value) list
  | Static_variant of string * (string * static_value) list
  | Static_array of static_value list
  | Static_storage of { element : Ground.ty; elements : static_value list; owned : bool }
      (** Elements in static memory, with the capacity recorded as the length when [owned], and as 0
          otherwise, as for a string's static bytes *)

type data = { data_key : Instance.key; ty : Ground.ty; value : static_value }

(* What an instance compiles to: code, or static data. *)
(* A capability [impl]'s table: its entries, in the order of the
   capability's methods. *)
type table = { table_key : Instance.key; entries : (Instance.key * signature) list }

(* Static evidence: its implementation, a value of zero size here, its
   table, and the evidence the implementation captured. *)
type evidence = { evidence_key : Instance.key; table : Instance.key; outer : Instance.key list }
type compiled = Code of t | Data of data | Table of table | Evidence of evidence

let signature (f : function_) =
  {
    parameters = List.map (fun local -> f.locals.(local).ty) f.parameters;
    result = f.result;
    returns = f.returns;
  }

let bug format = Printf.ksprintf (fun message -> invalid_arg ("Lir: " ^ message)) format

(* A cursor always holds its state, which lets code over a cursor that holds
   another be lowered before the cursor's fields are known. *)
let erased env = function
  | Value (Cursor _) -> false
  | Value ty -> (Memory_layout.of_type env ty).size = 0
  | Pointer _ | Raw _ | Environment _ | Evidence _ -> false

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

let target_operands = function
  | Indirect { value; _ } | Evidence_call { evidence = value; _ } -> [ value ]
  | Table_call { table; value; _ } -> [ table; value ]
  | Direct _ | Intrinsic _ -> []

let successors = function
  | Goto block -> [ block ]
  | Switch { cases; default; _ } -> List.map snd cases @ Option.to_list default
  | Switch_variant { cases; default; _ } -> List.map snd cases @ Option.to_list default
  | Return _ | Unreachable | Fail _ -> []
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
  | Moved_address p -> Moved_address (map_place ~place ~block p)
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
  | Evidence_call { evidence; slot; signature } ->
      Evidence_call { evidence = map_operand ~place ~block evidence; slot; signature }
  | Table_call { table; value; slot; signature } ->
      Table_call
        {
          table = map_operand ~place ~block table;
          value = map_operand ~place ~block value;
          slot;
          signature;
        }
  | (Direct _ | Intrinsic _) as target -> target

let map_destination ~place ~block = function
  | Discarded -> Discarded
  | Returned p -> Returned (map_place ~place ~block p)
  | Written p -> Written (map_place ~place ~block p)

let map_statement ~place ~block = function
  | Assign (p, rvalue) -> Assign (map_place ~place ~block p, map_rvalue ~place ~block rvalue)
  | Call { target; arguments; result } ->
      Call
        {
          target = map_target ~place ~block target;
          arguments = List.map (map_operand ~place ~block) arguments;
          result = map_destination ~place ~block result;
        }
  | Drop p -> Drop (map_place ~place ~block p)
  | Free_block { place = p; variant } -> Free_block { place = map_place ~place ~block p; variant }
  | Echo { text; length; site } ->
      Echo
        { text = map_operand ~place ~block text; length = map_operand ~place ~block length; site }

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
  | Fail { failure; message; length; site } ->
      Fail { failure; message = operand message; length = operand length; site }
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
  {
    f with
    parameters = List.map map_local f.parameters;
    written_result = Option.map map_local f.written_result;
    locals;
    blocks;
  }

let canonical_instance t = { t with main = canonical t.main; nested = Array.map canonical t.nested }
