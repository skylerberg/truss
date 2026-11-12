val version : int

type encoders = { path : Path.t -> Cbor.t; instance : Instance.key -> Cbor.t }

val equal_signature : Ir.signature -> Ir.signature -> bool
val encode : ?path:(Path.t -> Cbor.t) -> ?instance:(Instance.key -> Cbor.t) -> Ir.t -> Cbor.t

val encode_data :
  ?path:(Path.t -> Cbor.t) -> ?instance:(Instance.key -> Cbor.t) -> Ir.data -> Cbor.t

val encode_table :
  ?path:(Path.t -> Cbor.t) -> ?instance:(Instance.key -> Cbor.t) -> Ir.table -> Cbor.t

val hash : Ir.t -> string
