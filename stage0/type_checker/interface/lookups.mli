type t = {
  names : Resolve.Names.lookups;
  resolved : Resolve.section -> Resolve.Names.key -> Resolve.resolved;
  trait_header : Path.t -> Resolve.trait_header option;
  constant_value : Path.t -> Z.t option;
  header : Resolve.Names.key -> Environment.header option;
  elaborated_interface : Resolve.Names.key -> Environment.elaborated_interface;
  derived_interface : type_:Path.t -> trait:Path.t -> Types.impl_interface option;
  type_facts : Path.t -> Environment.type_facts option;
  granted : Path.package -> Path.package -> Environment.grant option;
}
