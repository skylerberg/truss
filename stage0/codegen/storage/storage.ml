let named builtin element : Ground.ty =
  Named { path = Intrinsic.builtin_path builtin; arguments = [ Type element ] }

let of_elements element = named Storage element
let view_of_elements element = named View element

let elements_of (ty : Ground.ty) =
  match ty with
  | Named { path; arguments = [ Type element ] } when Intrinsic.builtin_of_path path = Some Storage
    ->
      Some element
  | _ -> None

let viewed (ty : Ground.ty) =
  match ty with
  | Named { path; arguments = [ Type element ] } when Intrinsic.builtin_of_path path = Some View ->
      Some element
  | _ -> None

type representation =
  | Shape of Memory_layout.shape
  | Storage of Ground.ty
  | Handle
  | Shared of Ground.ty

let representation env (ty : Ground.ty) =
  match (elements_of ty, ty) with
  | Some element, _ -> Storage element
  | None, Named { path; arguments = [] } when Intrinsic.builtin_of_path path = Some Handle -> Handle
  | None, Named { path; arguments = [ Type value ] }
    when Intrinsic.builtin_of_path path = Some Shared ->
      Shared value
  | None, _ -> Shape (Memory_layout.shape env ty)

let buffer_field = "buffer"
let length_field = "length"
let capacity_field = "capacity"
let elements_field = "elements"

let shape ~uint64 element : Memory_layout.shape =
  Record
    [
      (buffer_field, Raw (Pointer (Data element)));
      (length_field, Typed uint64);
      (capacity_field, Typed uint64);
    ]

let view_shape ~uint64 element : Memory_layout.shape =
  Record [ (elements_field, Raw (Pointer (Data element))); (length_field, Typed uint64) ]

let ( / ) (place : Lowered.place) projection : Lowered.place =
  { place with projections = place.projections @ [ projection ] }

let constant_uint64 number = Lowered.Constant (Integer (UInt64, Z.of_int number))
let buffer storage = storage / Lowered.Field buffer_field
let length storage = storage / Lowered.Field length_field
let capacity storage = storage / Lowered.Field capacity_field
let at storage index = buffer storage / Index index
let view_elements view = view / Lowered.Field elements_field
let view_length view = view / Lowered.Field length_field
let view_at view index = view_elements view / Index index

let owning ty ~buffer ~length ~capacity : Lowered.rvalue =
  Build
    {
      ty;
      variant = None;
      fields = [ (buffer_field, buffer); (length_field, length); (capacity_field, capacity) ];
    }

let static ty ~elements ~length = owning ty ~buffer:elements ~length ~capacity:(constant_uint64 0)
let empty ty = static ty ~elements:(Constant (Bytes "")) ~length:(constant_uint64 0)

let view ty ~elements ~length : Lowered.rvalue =
  Build { ty; variant = None; fields = [ (elements_field, elements); (length_field, length) ] }
