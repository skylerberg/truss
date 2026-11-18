val list_own_methods : Lookups.t -> Path.t -> string -> (Path.receiver * Path.t) list
val find_own_constant : Lookups.t -> Path.t -> string -> Path.t option
val list_trait_methods : Lookups.t -> Path.t -> string -> Types.trait_method list
val list_trait_generics : Lookups.t -> Path.t -> Types.generic list
val read_method_signature : Lookups.t -> Path.t -> Types.trait_method -> Types.signature
val find_fields : Lookups.t -> Path.t -> Types.argument list -> Types.field list option
val find_variants : Lookups.t -> Path.t -> Types.argument list -> Types.variant list option
val are_fields_visible : Lookups.t -> package:Path.package -> Path.t -> bool
