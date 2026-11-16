let make_named builtin element : Ground.ty =
  Named { path = Intrinsic.make_builtin_path builtin; arguments = [ Type element ] }

let make_storage_type element = make_named Storage element
let make_view_type element = make_named View element

let match_element builtin (ty : Ground.ty) =
  match ty with
  | Named { path; arguments = [ Type element ] } when Intrinsic.builtin_of_path path = Some builtin
    ->
      Some element
  | _ -> None

let match_storage_element ty = match_element Storage ty
let match_view_element ty = match_element View ty
let buffer_field = "buffer"
let length_field = "length"
let capacity_field = "capacity"
let elements_field = "elements"

let make_storage_shape ~uint64 element : Memory_layout.shape =
  Record
    [
      (buffer_field, Raw (Pointer (Data element)));
      (length_field, Typed uint64);
      (capacity_field, Typed uint64);
    ]

let make_view_shape ~uint64 element : Memory_layout.shape =
  Record [ (elements_field, Raw (Pointer (Data element))); (length_field, Typed uint64) ]

let project_buffer storage = Lowered.project storage (Lowered.Field buffer_field)
let project_length storage = Lowered.project storage (Lowered.Field length_field)
let project_capacity storage = Lowered.project storage (Lowered.Field capacity_field)
let index_element storage index = Lowered.project (project_buffer storage) (Index index)
let project_view_elements view = Lowered.project view (Lowered.Field elements_field)
let project_view_length view = Lowered.project view (Lowered.Field length_field)
let index_view_element view index = Lowered.project (project_view_elements view) (Index index)

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
  build_storage ty ~buffer:(Constant (Bytes "")) ~length:(Lowered.make_uint64_constant 0)
    ~capacity:(Lowered.make_uint64_constant 0)

let build_view ty ~elements ~length : Lowered.rvalue =
  Build { ty; variant = None; fields = [ (elements_field, elements); (length_field, length) ] }
