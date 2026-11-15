type lookups = { interface : Interface.Lookups.t; mir : Parts.lookups }

val traits_with_required : Interface.Lookups.t -> Path.t -> Path.t list
val written_methods : Resolve.Names.lookups -> Path.t -> Path.t list
val impls_for : Interface.Lookups.t -> Path.package -> Path.t list -> Types.ty -> Path.t list
val impls_used : Interface.Lookups.t -> Path.package -> 'a Core.target -> Path.t list
val dispatched : 'a Core.target -> bool
val of_path : lookups -> Path.t -> Path.t list
val implementations : lookups -> visible:Path.package list -> Path.t -> Path.t list
