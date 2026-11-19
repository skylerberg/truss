type member =
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
  | Integer
  | Character

type t

val empty : t
val make : member list -> t
val list_members : t -> member list
val inter : t -> t -> t
val union : t -> t -> t
val is_empty : t -> bool
val is_subset : t -> of_:t -> bool
val mem : member -> t -> bool
val equal : t -> t -> bool
val find_single : t -> member option
val signed_integers : t
val unsigned_integers : t
val fixed_width_integers : t
val floats : t
val code_numbers : t
val negatable : t
val find_member : Types.ty -> member option
val make_type : member -> Types.ty
val find_range : member -> (Z.t * Z.t) option
val find_common_range : t -> (Z.t * Z.t) option
val list_fitting_integers : Z.t -> t
val find_sealed_implementors : Path.t -> t option
val find_bound_implementors : Types.trait_reference list -> t option
val choose_default : t -> member option
val describe : t -> string
