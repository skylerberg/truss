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

let buffer_field = "buffer"
let length_field = "length"
let capacity_field = "capacity"
let elements_field = "elements"

let shape ~usize element : Memory_layout.shape =
  Record
    [
      (buffer_field, Raw (Pointer (Data element)));
      (length_field, Typed usize);
      (capacity_field, Typed usize);
    ]

let view_shape ~usize element : Memory_layout.shape =
  Record [ (elements_field, Raw (Pointer (Data element))); (length_field, Typed usize) ]

let ( / ) (place : Lowered.place) projection : Lowered.place =
  { place with projections = place.projections @ [ projection ] }

let usize number = Lowered.Constant (Integer (USize, Z.of_int number))
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

let static ty ~elements ~length = owning ty ~buffer:elements ~length ~capacity:(usize 0)
let empty ty = static ty ~elements:(Constant (Bytes "")) ~length:(usize 0)

let view ty ~elements ~length : Lowered.rvalue =
  Build { ty; variant = None; fields = [ (elements_field, elements); (length_field, length) ] }
