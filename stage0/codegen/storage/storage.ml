let make_storage_type element = Ground.make_builtin Storage ~arguments:[ Type element ]
let make_view_type element = Ground.make_builtin View ~arguments:[ Type element ]

let find_element builtin (ty : Ground.ty) =
  match ty with
  | Named { path; arguments = [ Type element ] } when Intrinsic.find_builtin path = Some builtin ->
      Some element
  | _ -> None

let find_storage_element ty = find_element Storage ty
let find_view_element ty = find_element View ty
let buffer_field = "buffer"
let length_field = "length"
let capacity_field = "capacity"
let empty_buffer : Lowered.constant = Bytes ""
let uint64 = Ground.make_builtin UInt64

let make_storage_shape element : Memory_layout.shape =
  Record
    [
      (buffer_field, Raw (Pointer (Data element)));
      (length_field, Typed uint64);
      (capacity_field, Typed uint64);
    ]

let make_view_shape element : Memory_layout.shape =
  Record [ (buffer_field, Raw (Pointer (Data element))); (length_field, Typed uint64) ]

let project_buffer sequence = Lowered.project sequence (Lowered.Field buffer_field)
let project_length sequence = Lowered.project sequence (Lowered.Field length_field)
let project_capacity storage = Lowered.project storage (Lowered.Field capacity_field)
let index_element sequence index = Lowered.project (project_buffer sequence) (Index index)

let build_is_allocated storage : Lowered.rvalue =
  Binary (Not_equal, Copy (project_capacity storage), Lowered.make_uint64_constant 0)

let build_storage ty ~buffer ~length ~capacity : Lowered.rvalue =
  Build
    {
      ty;
      variant = None;
      fields = [ (buffer_field, buffer); (length_field, length); (capacity_field, capacity) ];
    }

let build_empty ty =
  build_storage ty ~buffer:(Constant empty_buffer) ~length:(Lowered.make_uint64_constant 0)
    ~capacity:(Lowered.make_uint64_constant 0)

let build_view ty ~buffer ~length : Lowered.rvalue =
  Build { ty; variant = None; fields = [ (buffer_field, buffer); (length_field, length) ] }
