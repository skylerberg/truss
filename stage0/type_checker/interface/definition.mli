val header :
  Lookups.t ->
  Resolve.Names.key ->
  (Environment.header, Diagnostic.in_definition list) result option

val lower : Lookups.t -> Resolve.Names.key -> Environment.lowered_interface option
val interface : Lookups.t -> Path.t -> Environment.interface option

val in_declared_order :
  Lookups.t -> Path.t -> variant:string option -> name:('a -> string) -> 'a list -> 'a list

val type_interface : Lookups.t -> Path.t -> Types.type_interface option
val signature : Lookups.t -> Path.t -> Types.signature option
val method_signature : Lookups.t -> owner:Path.t -> Types.trait_method -> Types.signature
val trait_interface : Lookups.t -> Path.t -> Types.trait_interface option
val make_self_parameter : Path.t -> Types.parameter
val impl_interface : Lookups.t -> Path.t -> Types.impl_interface option
val constant_type : Lookups.t -> Path.t -> Types.ty option
val test_uses : Lookups.t -> Path.t -> Types.capability_set option
