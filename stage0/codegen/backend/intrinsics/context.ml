let raise_bug format = Compiler_bug.raise_bug ~stage:"Intrinsics" format

type argument = Place of Lowered.place | Value of Lowered.operand
type types = { uint64 : Ground.ty; string_slice : Ground.ty }

type t = {
  env : Memory_layout.env;
  builder : Emit_c.Ir_builder.t;
  types : types;
  operation : Intrinsic.operation;
  type_arguments : Ground.ty list;
  value_arguments : Z.t list;
  arguments : argument list;
  destination : Lowered.place option;
  site : Lowered.site;
  reported : Lowered.operand option;
  trace : Lowered.operand option;
}

let make_operand = function Place place -> Lowered.Copy place | Value operand -> operand

let extract_place = function
  | Place place -> place
  | Value _ -> raise_bug "an operation on storage given a value"

let read = function
  | Place place | Value (Copy place) -> place
  | Value _ -> raise_bug "a value to read that is in no place"

let classify_scalar env (ty : Ground.ty) =
  match (Memory_layout.of_type env ty).form with
  | Scalar scalar -> scalar
  | _ -> raise_bug "%s is not a number" (Ground.to_string ty)

let set context rvalue =
  Option.iter
    (fun destination -> Emit_c.Ir_builder.emit context.builder (Assign (destination, rvalue)))
    context.destination

let read_argument context position = List.nth context.arguments position
let read_operand context position = make_operand (read_argument context position)

let read_type_argument context position =
  match List.nth_opt context.type_arguments position with
  | Some ty -> ty
  | None -> raise_bug "a missing type argument"

let call context ?result intrinsic arguments =
  let result = match result with Some place -> Lowered.Returned place | None -> Discarded in
  Emit_c.Ir_builder.emit context.builder (Call { target = Intrinsic intrinsic; arguments; result })

let allocate_uint64_local context =
  Emit_c.Ir_builder.allocate_local context.builder (Value context.types.uint64)

let emit_uint64 context rvalue =
  Emit_c.Ir_builder.emit_temporary context.builder (Value context.types.uint64) rvalue

let emit_bool context rvalue = Emit_c.Ir_builder.emit_temporary context.builder (Raw Bool) rvalue
let copy_length sequence = Lowered.Copy (Storage.project_length sequence)

let fail context failure message =
  Emit_c.Ir_builder.finish context.builder
    (Fail
       {
         failure;
         message = Constant (Bytes message);
         length = Lowered.make_uint64_constant (String.length message);
         site = context.site;
         reported = context.reported;
         trace = context.trace;
       })

let fail_when context failure condition message =
  let failed = Emit_c.Ir_builder.allocate_block context.builder
  and after = Emit_c.Ir_builder.allocate_block context.builder in
  Emit_c.Ir_builder.branch context.builder condition ~yes:failed ~no:after;
  Emit_c.Ir_builder.start context.builder failed;
  fail context failure message;
  Emit_c.Ir_builder.start context.builder after

let fail_obligation_when context condition message = fail_when context Obligation condition message

let check_index context index count =
  fail_obligation_when context (Test (Greater_equal, index, count)) "index out of bounds"

let compute_room context storage =
  emit_uint64 context
    (Binary (Subtract, Copy (Storage.project_capacity storage), copy_length storage))

let read_array_length context =
  match context.value_arguments with
  | [ count ] -> count
  | _ -> raise_bug "%s without the array's length" (Intrinsic.show_operation context.operation)
