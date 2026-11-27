type t =
  | Int8
  | Int16
  | Int32
  | Int64
  | UInt8
  | UInt16
  | UInt32
  | UInt64
  | Float32
  | Float64
  | Bool
  | Character
  | Unit
  | Never
  | Integer
  | Array
  | Storage
  | View
  | Handle
  | Shared

let all =
  [
    Int8;
    Int16;
    Int32;
    Int64;
    UInt8;
    UInt16;
    UInt32;
    UInt64;
    Float32;
    Float64;
    Bool;
    Character;
    Unit;
    Never;
    Integer;
    Array;
    Storage;
    View;
    Handle;
    Shared;
  ]

let show = function
  | Int8 -> "Int8"
  | Int16 -> "Int16"
  | Int32 -> "Int32"
  | Int64 -> "Int64"
  | UInt8 -> "UInt8"
  | UInt16 -> "UInt16"
  | UInt32 -> "UInt32"
  | UInt64 -> "UInt64"
  | Float32 -> "Float32"
  | Float64 -> "Float64"
  | Bool -> "Bool"
  | Character -> "Character"
  | Unit -> "Unit"
  | Never -> "Never"
  | Integer -> "Integer"
  | Array -> "Array"
  | Storage -> "Storage"
  | View -> "View"
  | Handle -> "Handle"
  | Shared -> "Shared"

let find_scalar_literal tag text =
  let rec list_scalars index scalars =
    if index >= String.length text then List.rev scalars
    else
      let decoded = String.get_utf_8_uchar text index in
      list_scalars
        (index + Uchar.utf_decode_length decoded)
        (Uchar.utf_decode_uchar decoded :: scalars)
  in
  match (list_scalars 0 [], tag) with
  | [ scalar ], Character -> Some (Uchar.to_int scalar)
  | [ scalar ], UInt8 when Uchar.to_int scalar < 128 -> Some (Uchar.to_int scalar)
  | _ -> None
