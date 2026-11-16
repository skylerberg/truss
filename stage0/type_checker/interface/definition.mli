val is_specification : Environment.interface -> bool
val find_interface : Lookups.t -> Path.t -> Environment.interface option

val sort_in_declared_order :
  Lookups.t -> Path.t -> variant:string option -> name_of:('a -> string) -> 'a list -> 'a list

val find_type_interface : Lookups.t -> Path.t -> Types.type_interface option
val read_type_interface : Lookups.t -> Path.t -> Types.type_interface
val find_declared_signature : Lookups.t -> Path.t -> Types.signature option
val read_method_signature : Lookups.t -> owner:Path.t -> Types.trait_method -> Types.signature
val find_trait_interface : Lookups.t -> Path.t -> Types.trait_interface option
val read_trait_interface : Lookups.t -> Path.t -> Types.trait_interface
val find_impl_interface : Lookups.t -> Path.t -> Types.impl_interface option
val read_impl_interface : Lookups.t -> Path.t -> Types.impl_interface
val find_constant_type : Lookups.t -> Path.t -> Types.ty option
val read_constant_type : Lookups.t -> Path.t -> Types.ty
val read_test_uses : Lookups.t -> Path.t -> Types.capability_set
val is_external_test : Lookups.t -> Path.t -> bool
val find_real_implementation : Lookups.t -> Path.t -> Path.t option

val find_trait_method :
  Lookups.t -> Path.t -> name:string -> receiver:Path.receiver -> Types.trait_method option
