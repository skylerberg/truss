type lookups = { interface : Interface.Lookups.t; mir : Parts.lookups }

val list_traits_with_required : Interface.Lookups.t -> Path.t -> Path.t list
val list_written_methods : Resolve.Names.lookups -> Path.t -> Path.t list
val list_impl_methods : Interface.Lookups.t -> Path.t -> Path.t list
val defines : Resolve.Names.lookups -> Path.t -> Path.t -> bool
val list_impls_for : Interface.Lookups.t -> Path.package -> Path.t list -> Types.ty -> Path.t list
val list_impls_used : Interface.Lookups.t -> Path.package -> 'a Core.target -> Path.t list
val is_dispatched : 'a Core.target -> bool
val list_path_edges : lookups -> Path.t -> Path.t list
val list_implementations : lookups -> calling_package:Path.package -> Path.t -> Path.t list
