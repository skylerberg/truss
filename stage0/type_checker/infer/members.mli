val own_methods : Lookups.t -> Path.t -> string -> (Path.receiver * Path.t) list
val own_constant : Lookups.t -> Path.t -> string -> Path.t option
val trait_methods : Lookups.t -> Path.t -> string -> Types.trait_method list
val trait_method : Lookups.t -> Path.t -> string -> Path.receiver -> Types.trait_method option
val method_signature : Lookups.t -> Path.t -> Types.trait_method -> Types.signature
val fields : Lookups.t -> Path.t -> Types.argument list -> Types.field list option
val variants : Lookups.t -> Path.t -> Types.argument list -> Types.variant list option
val fields_visible : Lookups.t -> package:Path.package -> Path.t -> bool
