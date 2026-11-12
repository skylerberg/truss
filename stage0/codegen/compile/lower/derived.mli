val derived :
  Definitions.context ->
  key:Instance.key ->
  type_path:Path.t ->
  trait:Path.t ->
  name:string ->
  type_arguments:Ground.argument list ->
  Lir.t
