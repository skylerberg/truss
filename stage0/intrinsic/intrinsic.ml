let module_ : Path.module_ = { package = "standard"; modules = [ "intrinsic" ] }

type builtin =
  | Int8
  | Int16
  | Int32
  | Int64
  | UInt8
  | UInt16
  | UInt32
  | UInt64
  | USize
  | ISize
  | Float32
  | Float64
  | Bool
  | Character
  | Unit
  | Never
  | Integer
  | Array

let builtins =
  [
    Int8;
    Int16;
    Int32;
    Int64;
    UInt8;
    UInt16;
    UInt32;
    UInt64;
    USize;
    ISize;
    Float32;
    Float64;
    Bool;
    Character;
    Unit;
    Never;
    Integer;
    Array;
  ]

let builtin_name = function
  | Int8 -> "Int8"
  | Int16 -> "Int16"
  | Int32 -> "Int32"
  | Int64 -> "Int64"
  | UInt8 -> "UInt8"
  | UInt16 -> "UInt16"
  | UInt32 -> "UInt32"
  | UInt64 -> "UInt64"
  | USize -> "USize"
  | ISize -> "ISize"
  | Float32 -> "Float32"
  | Float64 -> "Float64"
  | Bool -> "Bool"
  | Character -> "Character"
  | Unit -> "Unit"
  | Never -> "Never"
  | Integer -> "Integer"
  | Array -> "Array"

let builtin_path builtin = Path.Top { module_; name = builtin_name builtin }

let builtin_of_path = function
  | Path.Top { module_ = m; name } when m = module_ ->
      List.find_opt (fun builtin -> builtin_name builtin = name) builtins
  | _ -> None
