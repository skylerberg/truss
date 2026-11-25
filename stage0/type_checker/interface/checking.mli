type state = {
  lookups : Lookups.t;
  key : Resolve.Names.key;
  definition : Syntax.definition;
  elaborated : Environment.elaborated_interface;
  diagnostics : Catalog.diagnostic list ref;
}

val report : state -> Catalog.Typing.t -> unit
val list_bounds : state -> Impls.bounds
val find_evidence : state -> Types.ty -> Types.trait_reference -> Impls.solution option
