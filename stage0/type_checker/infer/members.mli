val lookup_member : State.state -> Path.t -> Path.t Resolve.Names.lookup
val lookup_method : State.state -> Path.t -> string -> Path.receiver -> Path.t Resolve.Names.lookup
val list_member_lookups : State.state -> Path.t -> string -> Path.t Resolve.Names.lookup list
val list_methods : Path.t -> string -> Path.t list
val has_visible_method : State.state -> Path.t -> string -> bool

val make_hidden_error :
  State.state -> Source.Definition_span.t -> Path.t * Resolve.Names.visibility -> Types.ty

val list_trait_methods : Lookups.t -> Path.t -> string -> Types.trait_method list
val list_trait_generics : Lookups.t -> Path.t -> Types.generic list

val read_method_signature :
  Signatures.t -> Lookups.t -> Path.t -> Types.trait_method -> Types.signature

val find_fields : Lookups.t -> Path.t -> Types.argument list -> Types.field list option
val find_variants : Lookups.t -> Path.t -> Types.argument list -> Types.variant list option
val are_fields_visible : Lookups.t -> package:Path.package -> Path.t -> bool
val is_tuple_type : Lookups.t -> Path.t -> bool
